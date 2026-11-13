#!/usr/bin/env node
// Lean Lens helper: runs real Lean on your machine for the code you are reading on GitHub.
//
// For a repository, a commit and some Lean files, it fetches the commit into its own cache,
// prepares the project (Lean version, Mathlib cache, the files' imports), elaborates each file
// with SubVerso's `subverso-extract-mod` and keeps the result: what Lean knows about every
// token, and the proof state at every tactic. The extension asks for that over localhost.
//
//   node lean-lens-helper.mjs [--port 5326] [--allow owner/repo] [--link owner/repo=/checkout]
//   node lean-lens-helper.mjs run --repo owner/repo --sha <commit> [--pr N] File.lean …
//
// Elaborating a Lean file runs the code in it. The helper therefore only works on repositories
// you have allowed, only when asked with its token, and never on its own initiative. On macOS
// that code runs in a sandbox: no network, no access to your files (see `seatbeltProfile`).

import http from 'node:http';
import { spawn } from 'node:child_process';
import { createHash, randomBytes, timingSafeEqual } from 'node:crypto';
import { chmodSync, existsSync, mkdirSync, readFileSync, realpathSync, renameSync, rmSync, writeFileSync } from 'node:fs';
import { availableParallelism, homedir } from 'node:os';
import path from 'node:path';
import { pathToFileURL } from 'node:url';
import { parseArgs } from 'node:util';

import { DATA_FORMAT_VERSION, convertModule } from './convert.mjs';

export const HELPER_VERSION = 1;
export const DEFAULT_PORT = 5326;
const DEFAULT_SUBVERSO = 'https://github.com/leanprover/subverso.git';
const DEFAULT_CLONE_BASE = 'https://github.com/';
// SubVerso's JSON is not a stable format, so the revision is pinned. Conversion checks itself
// (see convert.mjs), so a revision with another format gives errors rather than wrong hovers.
const DEFAULT_SUBVERSO_REV = '892d6dc520270b5fb8c1291dd1b131e8c16255ed';
const EXTRACT_TIMEOUT_MS = 20 * 60 * 1000;
const MAX_BODY_BYTES = 1024 * 1024;

// ---------------------------------------------------------------------------------------------
// Checks on what a request names. Everything here ends up in a path or a command's arguments.

export const isRepo = (value) => typeof value === 'string' && value.length < 200 &&
  /^[A-Za-z0-9][A-Za-z0-9_.-]*\/[A-Za-z0-9_.][A-Za-z0-9_.-]*$/.test(value) && !value.includes('..');
export const isSha = (value) => typeof value === 'string' && /^[0-9a-f]{40}$/.test(value);
export const isLeanPath = (value) => typeof value === 'string' && value.length < 512 && value.endsWith('.lean') &&
  !value.includes('\\') && !value.includes('\0') && value.split('/').every((part) => part && part !== '.' && part !== '..');

export const sha256 = (text) => createHash('sha256').update(text).digest('hex');

/** Modules a Lean file imports, read from its header only (so `import` in a comment or string is not one). */
export function importsOf(source) {
  const imports = [];
  let depth = 0; // nesting of /- … -/
  for (const raw of source.split('\n')) {
    let line = raw;
    let code = '';
    for (let i = 0; i < line.length; i++) {
      if (line.startsWith('/-', i)) { depth += 1; i += 1; continue; }
      if (depth > 0 && line.startsWith('-/', i)) { depth -= 1; i += 1; continue; }
      if (depth === 0) {
        if (line.startsWith('--', i)) break;
        code += line[i];
      }
    }
    line = code.trim();
    if (!line || line === 'module' || line === 'prelude') continue;
    const match = line.match(/^(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(\S+)$/);
    if (!match) break; // the header ends at the first command
    imports.push(match[1]);
  }
  return imports;
}

/** The directory of the Lake project a file belongs to (relative to the checkout), or null. */
export function lakeRootFor(checkout, file) {
  const parts = file.split('/').slice(0, -1);
  for (let depth = parts.length; depth >= 0; depth--) {
    const dir = parts.slice(0, depth).join('/');
    if (['lakefile.lean', 'lakefile.toml'].some((name) => existsSync(path.join(checkout, dir, name)))) return dir;
  }
  return null;
}

/** A file's module name, from the source roots Lake sets up (`LEAN_SRC_PATH`), or null. */
export function moduleNameFor(root, srcPath, file) {
  const real = (p) => { try { return realpathSync(p); } catch { return path.resolve(p); } };
  const base = real(root);
  const absolute = path.join(base, file);
  let best = null;
  for (const entry of (srcPath || '').split(path.delimiter).filter(Boolean)) {
    const relative = path.relative(real(path.resolve(base, entry)), absolute);
    if (relative.startsWith('..') || path.isAbsolute(relative)) continue;
    if (best === null || relative.length < best.length) best = relative;
  }
  return best === null ? null : best.replace(/\.lean$/, '').split(path.sep).join('.');
}

/** Whether a Lake project is Mathlib or depends on it (so `lake exe cache get` applies). */
export function usesMathlib(manifestText) {
  try {
    const manifest = JSON.parse(manifestText);
    return manifest.name === 'mathlib' || (manifest.packages || []).some((p) => p.name === 'mathlib');
  } catch {
    return false;
  }
}

// ---------------------------------------------------------------------------------------------
// Running commands.

const tail = (text, n = 600) => (text.length > n ? `…${text.slice(-n)}` : text).trim();

/** Run a command (never through a shell). Resolves to `{code, stdout, stderr}`. */
function run(command, args, { cwd, env, onLine, timeoutMs } = {}) {
  return new Promise((resolve) => {
    const child = spawn(command, args, {
      cwd,
      env: env || { ...process.env, GIT_TERMINAL_PROMPT: '0' },
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    const kept = { stdout: '', stderr: '' };
    const feed = (which) => (chunk) => {
      const text = chunk.toString('utf8');
      kept[which] = (kept[which] + text).slice(-64 * 1024 * 1024);
      if (onLine) for (const line of text.split('\n')) if (line.trim()) onLine(line.trim());
    };
    child.stdout.on('data', feed('stdout'));
    child.stderr.on('data', feed('stderr'));
    const timer = timeoutMs ? setTimeout(() => child.kill('SIGKILL'), timeoutMs) : null;
    child.on('error', (error) => { if (timer) clearTimeout(timer); resolve({ code: -1, stdout: kept.stdout, stderr: error.message }); });
    child.on('close', (code, signal) => {
      if (timer) clearTimeout(timer);
      resolve({ code: code === null ? -1 : code, signal, stdout: kept.stdout, stderr: kept.stderr });
    });
  });
}

async function must(command, args, options) {
  const result = await run(command, args, options);
  if (result.code !== 0) {
    throw new Error(`\`${command} ${args.slice(0, 4).join(' ')}\` failed: ${tail(result.stderr || result.stdout) || `exit ${result.code}`}`);
  }
  return result;
}

/** Copy a directory tree without using more disk where the file system can share blocks. */
async function cloneTree(from, to) {
  const attempts = process.platform === 'darwin'
    ? [['cp', ['-cRp', from, to]], ['cp', ['-Rp', from, to]]]
    : [['cp', ['-a', '--reflink=auto', from, to]]];
  let last = null;
  for (const [command, args] of attempts) {
    last = await run(command, args);
    if (last.code === 0) return;
    rmSync(to, { recursive: true, force: true });
  }
  throw new Error(`Could not copy ${from}: ${tail(last.stderr)}`);
}

// ---------------------------------------------------------------------------------------------
// The sandbox. `lake` evaluates a project's lakefile and elaborating a file runs the code in it,
// so both run where they can do little: no network except while fetching dependencies, no
// writing outside the project's copy, and no reading of the user's own files.

const realOrSame = (target) => { try { return realpathSync(target); } catch { return path.resolve(target); } };

function ancestorsOf(target) {
  const out = [];
  for (let dir = path.dirname(target); dir !== path.dirname(dir); dir = path.dirname(dir)) out.push(dir);
  return out;
}

/**
 * A macOS sandbox profile (for `sandbox-exec`). Under it a command can read system files and
 * the `readable` and `writable` paths, but nothing else under the home directories, mounted
 * volumes or the temporary directories; it can write only to the `writable` paths, except the
 * `guarded` ones inside them; and it has no network unless `network` is set. It also cannot
 * send Apple events to other applications.
 */
export function seatbeltProfile({ network = false, readable = [], writable = [], guarded = [], home = homedir() } = {}) {
  const quote = (target) => `"${target.replace(/[\\"]/g, '\\$&')}"`;
  const subpaths = (targets) => targets.map((target) => `(subpath ${quote(target)})`).join(' ');
  const visible = [...new Set([...readable, ...writable])];
  const above = [...new Set(visible.flatMap(ancestorsOf))];
  const hidden = [...new Set(['/Users', '/Volumes', '/private/tmp', '/private/var/folders', '/private/var/root', realOrSame(home)])];
  return [
    '(version 1)',
    '(allow default)',
    '(deny appleevent-send)',
    ...(network ? [] : ['(deny network*)']),
    '(deny file-write*)',
    `(allow file-write* (literal "/dev/null") (literal "/dev/zero") (literal "/dev/dtracehelper") (literal "/dev/tty") (regex #"^/dev/fd/") (regex #"^/dev/ttys[0-9]+")${writable.length ? ` ${subpaths(writable)}` : ''})`,
    ...(guarded.length ? [`(deny file-write* ${subpaths(guarded)})`] : []),
    `(deny file-read* ${subpaths(hidden)})`,
    // (An `allow` with no path would allow everything, so these lines need at least one.)
    ...(visible.length ? [`(allow file-read* ${subpaths(visible)})`] : []),
    ...(above.length ? [`(allow file-read-metadata ${above.map((target) => `(literal ${quote(target)})`).join(' ')})`] : []),
  ].join('\n');
}

/** How this machine can confine a command: 'seatbelt' (macOS), or null when it can't. */
async function detectSandbox() {
  if (process.platform !== 'darwin' || !existsSync('/usr/bin/sandbox-exec')) return null;
  const probe = await run('/usr/bin/sandbox-exec', ['-p', seatbeltProfile({ readable: ['/usr/bin'] }), '/usr/bin/true']);
  return probe.code === 0 ? 'seatbelt' : null;
}

// ---------------------------------------------------------------------------------------------
// Settings kept between runs.

export function defaultCacheDir() {
  if (process.env.LEAN_LENS_CACHE) return process.env.LEAN_LENS_CACHE;
  if (process.platform === 'darwin') return path.join(homedir(), 'Library', 'Caches', 'lean-lens');
  return path.join(process.env.XDG_CACHE_HOME || path.join(homedir(), '.cache'), 'lean-lens');
}

function loadConfig(cacheDir) {
  const file = path.join(cacheDir, 'config.json');
  let config = {};
  try { config = JSON.parse(readFileSync(file, 'utf8')); } catch { /* first run */ }
  if (typeof config.token !== 'string' || config.token.length < 20) config.token = randomBytes(24).toString('base64url');
  if (!Array.isArray(config.allow)) config.allow = [];
  if (!config.links || typeof config.links !== 'object') config.links = {};
  const save = () => {
    mkdirSync(cacheDir, { recursive: true });
    writeFileSync(file, `${JSON.stringify(config, null, 2)}\n`, { mode: 0o600 });
    try { chmodSync(file, 0o600); } catch { /* best effort */ }
  };
  save();
  return { config, save };
}

// ---------------------------------------------------------------------------------------------
// The helper itself.

/**
 * @param {object} options `{cacheDir, jobs, subverso, subversoRev, cloneBase, sandbox, log}`
 * @returns `{config, allow, link, start, status, fileState, readData, handle, sandbox}`
 */
export function createHelper(options = {}) {
  const cacheDir = path.resolve(options.cacheDir || defaultCacheDir());
  const { config, save } = loadConfig(cacheDir);
  const log = options.log || ((message) => console.log(`[${new Date().toTimeString().slice(0, 8)}] ${message}`));
  const poolSize = Math.max(1, Number(options.jobs) || Math.min(4, Math.ceil(availableParallelism() / 2)));
  const subverso = options.subverso || DEFAULT_SUBVERSO;
  const subversoRev = options.subversoRev || DEFAULT_SUBVERSO_REV;
  const cloneBase = (options.cloneBase || DEFAULT_CLONE_BASE).replace(/\/*$/, '/');
  // 'seatbelt' when commands can be confined, 'none' when this system can't, 'off' when asked not to.
  const sandboxWanted = options.sandbox !== false;
  let sandboxState = sandboxWanted ? 'checking' : 'off';
  const sandboxKind = sandboxWanted
    ? detectSandbox().then((kind) => { sandboxState = kind || 'none'; return kind; })
    : Promise.resolve(null);

  const repoQueues = new Map(); // repo → promise of its last job (one checkout per repository)
  const latestJob = new Map(); // repo@sha → the job last started for that commit
  const fileStates = new Map(); // repo@sha:path → {state: 'queued' | 'running' | 'error', error}
  const extractorBuilds = new Map(); // directory → promise of the extractor binary

  const repoDir = (repo) => path.join(cacheDir, 'repos', ...repo.split('/'));
  // Results are kept by data format, so a newer helper never serves an older format.
  const dataFile = (repo, sha, file) => path.join(cacheDir, 'data', `v${DATA_FORMAT_VERSION}`, ...repo.split('/'), sha, `${file}.json`);
  const fileKey = (repo, sha, file) => `${repo}@${sha}:${file}`;

  function allow(repo) {
    if (!isRepo(repo)) throw new Error(`Not a repository name: ${repo}`);
    if (!config.allow.includes(repo)) { config.allow.push(repo); save(); log(`Allowed ${repo}`); }
  }

  /** Use an existing checkout as the starting point for a repository (its commits and its build). */
  function link(repo, checkout) {
    if (!isRepo(repo)) throw new Error(`Not a repository name: ${repo}`);
    const resolved = path.resolve(checkout);
    if (!existsSync(path.join(resolved, '.git'))) throw new Error(`${resolved} is not a git checkout`);
    config.links[repo] = resolved;
    save();
  }

  // --- Preparing a checkout ------------------------------------------------------------------

  const depsStamp = (root) => sha256(['lean-toolchain', 'lake-manifest.json', 'lakefile.lean', 'lakefile.toml']
    .map((name) => { try { return readFileSync(path.join(root, name), 'utf8'); } catch { return ''; } }).join('\0'));
  // Which dependencies a project's copy was last prepared for. Kept outside the copy, which
  // the project's own code can write to.
  const stampFile = (repo, rootDir) => path.join(cacheDir, 'state', `${sha256(`${repo}\0${rootDir === '.' ? '' : rootDir}`).slice(0, 32)}.deps`);
  const writeStamp = (repo, rootDir, stamp) => {
    mkdirSync(path.join(cacheDir, 'state'), { recursive: true });
    writeFileSync(stampFile(repo, rootDir), stamp);
  };

  async function ensureRepo(job) {
    const dir = repoDir(job.repo);
    if (existsSync(path.join(dir, '.git'))) return dir;
    // Built in a staging directory, so an interrupted first run is not taken for a finished one.
    const staging = `${dir}.partial`;
    rmSync(dir, { recursive: true, force: true });
    rmSync(staging, { recursive: true, force: true });
    mkdirSync(path.dirname(dir), { recursive: true });
    const linked = config.links[job.repo];
    const remote = `${cloneBase}${job.repo}.git`;
    if (linked && existsSync(path.join(linked, '.git'))) {
      job.say(`Copying ${linked}`);
      await must('git', ['clone', '--quiet', '--no-checkout', linked, staging]);
      const origin = await run('git', ['-C', linked, 'remote', 'get-url', 'origin']);
      await must('git', ['-C', staging, 'remote', 'rename', 'origin', 'local']);
      await must('git', ['-C', staging, 'remote', 'add', 'origin', origin.code === 0 && origin.stdout.trim() ? origin.stdout.trim() : remote]);
      // The build too, so Lake only rebuilds what differs at the commit being read.
      const lakefiles = await run('git', ['-C', linked, 'ls-files', '--', 'lakefile.lean', 'lakefile.toml', '*/lakefile.lean', '*/lakefile.toml']);
      for (const lakefile of lakefiles.stdout.split('\n').filter(Boolean)) {
        const root = path.dirname(lakefile);
        const built = path.join(linked, root, '.lake');
        if (!existsSync(built)) continue;
        job.say(`Copying the build in ${root === '.' ? 'the project' : root} (shares disk space where it can)`);
        mkdirSync(path.join(staging, root), { recursive: true });
        await cloneTree(built, path.join(staging, root, '.lake'));
        writeStamp(job.repo, root, depsStamp(path.join(linked, root)));
      }
    } else {
      job.say(`Cloning ${remote}`);
      await must('git', ['clone', '--quiet', '--filter=blob:none', '--no-checkout', remote, staging]);
    }
    renameSync(staging, dir);
    return dir;
  }

  async function checkout(dir, job) {
    // (No hooks, whatever the copy's `.git` says: this runs outside the sandbox.)
    const git = ['-C', dir, '-c', 'core.hooksPath=/dev/null', '-c', 'core.fsmonitor=false'];
    const has = async () => (await run('git', [...git, 'cat-file', '-e', `${job.sha}^{commit}`])).code === 0;
    if (!(await has())) {
      job.say(`Fetching ${job.sha.slice(0, 10)}`);
      const remotes = (await run('git', [...git, 'remote'])).stdout.split('\n').filter(Boolean);
      if (remotes.includes('local')) await run('git', [...git, 'fetch', '--quiet', 'local']);
      if (!(await has())) await run('git', [...git, 'fetch', '--quiet', 'origin', job.sha]);
      if (!(await has()) && job.pr) await run('git', [...git, 'fetch', '--quiet', 'origin', `pull/${job.pr}/head`]);
      if (!(await has())) throw new Error(`Commit ${job.sha.slice(0, 10)} was not found in ${job.repo}`);
    }
    await must('git', [...git, 'checkout', '--quiet', '--force', '--detach', job.sha]);
  }

  // --- Running a project's code --------------------------------------------------------------

  const madeDir = (target) => { mkdirSync(target, { recursive: true }); return realOrSame(target); };
  const mathlibCacheDir = () => madeDir(process.env.MATHLIB_CACHE_DIR ||
    path.join(process.env.XDG_CACHE_HOME || path.join(homedir(), '.cache'), 'mathlib'));
  // The real `git`, for Lake's own cloning of dependencies: on macOS `/usr/bin/git` is a stub
  // that looks its tool up through files the sandbox hides.
  let gitDirectory = null;
  const gitDir = async () => {
    if (gitDirectory === null) {
      const found = process.platform === 'darwin' ? await run('/usr/bin/xcrun', ['-f', 'git']) : { code: 1 };
      gitDirectory = found.code === 0 && found.stdout.trim() ? path.dirname(found.stdout.trim()) : '';
    }
    return gitDirectory;
  };

  /**
   * Run a command that executes a project's code: `lake` (which evaluates the lakefile) or the
   * extractor (which elaborates a file). Its environment has none of the helper's own
   * variables, and its home directory is an empty one of the helper's. Where the system has a
   * sandbox, it can also read only the Lean toolchain and the paths given, write only where
   * told, and reach the network only when `network` is set.
   */
  async function untrusted(command, args, { cwd, toolchain, network = false, readable = [], writable = [], onLine, timeoutMs } = {}) {
    if (!sandboxWanted) return run(command, args, { cwd, onLine, timeoutMs });
    const home = madeDir(path.join(cacheDir, 'home'));
    const temporary = madeDir(path.join(cacheDir, 'tmp'));
    const env = {
      PATH: [toolchain && toolchain.bin, await gitDir(), '/usr/bin', '/bin', '/usr/sbin', '/sbin', '/opt/homebrew/bin', '/usr/local/bin'].filter(Boolean).join(path.delimiter),
      HOME: home,
      TMPDIR: temporary,
      LANG: process.env.LANG || 'en_US.UTF-8',
      GIT_TERMINAL_PROMPT: '0',
      MATHLIB_CACHE_DIR: process.env.MATHLIB_CACHE_DIR || path.join(process.env.XDG_CACHE_HOME || path.join(homedir(), '.cache'), 'mathlib'),
    };
    if ((await sandboxKind) !== 'seatbelt') return run(command, args, { cwd, env, onLine, timeoutMs });
    const allowed = [home, temporary, ...writable].map(realOrSame);
    const profile = seatbeltProfile({
      network,
      readable: [...(toolchain ? [toolchain.root] : []), ...readable].map(realOrSame),
      writable: allowed,
      // A checkout's own `.git` stays as it is: the helper runs `git` there later, outside the
      // sandbox, and a hook or setting planted now would run then.
      guarded: allowed.map((target) => path.join(target, '.git')),
    });
    return run('/usr/bin/sandbox-exec', ['-p', profile, command, ...args], { cwd, env, onLine, timeoutMs });
  }

  /** The Lean version a project pins. */
  function toolchainOf(root) {
    try {
      return readFileSync(path.join(root, 'lean-toolchain'), 'utf8').trim();
    } catch {
      throw new Error('This project has no lean-toolchain file, so its Lean version is unknown');
    }
  }

  /**
   * Where the project's Lean lives: `{ lake, bin, root }`, the real programs rather than elan's
   * stand-ins, so they can be run directly. elan only reads the project's `lean-toolchain` here
   * (and downloads that version if it is missing); nothing of the project is run.
   */
  async function resolveToolchain(root, job) {
    let found = await run('elan', ['which', 'lake'], { cwd: root });
    if (found.code !== 0 && found.code !== -1) {
      const name = toolchainOf(root);
      job.say(`Installing ${name}`);
      await must('elan', ['toolchain', 'install', name], { onLine: (line) => job.progress(line) });
      found = await must('elan', ['which', 'lake'], { cwd: root });
    }
    // Without elan, whichever `lake` is installed.
    if (found.code !== 0) found = await must('/usr/bin/which', ['lake']);
    const lake = realOrSame(found.stdout.trim().split('\n').pop());
    return { lake, bin: path.dirname(lake), root: path.dirname(path.dirname(lake)) };
  }

  async function ensureDependencies(root, rootDir, toolchain, job) {
    const stamp = depsStamp(root);
    try { if (readFileSync(stampFile(job.repo, rootDir), 'utf8') === stamp) return; } catch { /* not prepared yet */ }
    let manifest = '';
    try { manifest = readFileSync(path.join(root, 'lake-manifest.json'), 'utf8'); } catch { /* no dependencies */ }
    // The one step with network access: Lake clones the packages the manifest lists, and for a
    // Mathlib project its `cache` tool downloads the prebuilt files.
    const mathlib = usesMathlib(manifest);
    job.say(mathlib ? 'Downloading the Mathlib cache' : "Fetching the project's dependencies");
    const result = await untrusted(toolchain.lake, mathlib ? ['exe', 'cache', 'get'] : ['env', 'true'], {
      cwd: root, toolchain, network: true, writable: [job.dir, ...(mathlib ? [mathlibCacheDir()] : [])],
      onLine: (line) => job.progress(line),
    });
    if (result.code !== 0) job.note(`\`lake ${mathlib ? 'exe cache get' : 'env'}\` failed: ${tail(result.stderr || result.stdout, 300)}`);
    writeStamp(job.repo, rootDir, stamp);
  }

  async function buildImports(root, files, toolchain, job) {
    const imports = new Set();
    for (const file of files) {
      try { importsOf(readFileSync(path.join(root, file), 'utf8')).forEach((name) => imports.add(name)); } catch { /* reported when extracting */ }
    }
    if (!imports.size) return;
    job.say(`Building what ${files.length === 1 ? 'the file imports' : `${files.length} files import`}`);
    const result = await untrusted(toolchain.lake, ['build', ...[...imports].map((name) => `+${name}`)], {
      cwd: root, toolchain, writable: [job.dir], onLine: (line) => job.progress(line),
    });
    if (result.code !== 0) job.note(`\`lake build\` of the imports failed: ${tail(result.stderr || result.stdout, 400)}`);
  }

  /** The SubVerso extractor for a Lean version, built once and kept. */
  function ensureExtractor(root, toolchain, job) {
    const name = toolchainOf(root);
    const dir = path.join(cacheDir, 'extractors', `${name.replace(/[^A-Za-z0-9._-]+/g, '_')}-${subversoRev.slice(0, 12)}`);
    const binary = path.join(dir, '.lake', 'build', 'bin', 'subverso-extract-mod');
    if (existsSync(binary)) return Promise.resolve({ binary, dir });
    if (!extractorBuilds.has(dir)) {
      extractorBuilds.set(dir, (async () => {
        job.say(`Building the SubVerso extractor for ${name} (once per Lean version)`);
        rmSync(dir, { recursive: true, force: true });
        mkdirSync(path.dirname(dir), { recursive: true });
        await must('git', ['clone', '--quiet', '--no-checkout', subverso, dir]);
        await must('git', ['-C', dir, 'checkout', '--quiet', subversoRev]);
        writeFileSync(path.join(dir, 'lean-toolchain'), `${name}\n`);
        const built = await untrusted(toolchain.lake, ['build', 'subverso-extract-mod'], {
          cwd: dir, toolchain, writable: [dir], onLine: (line) => job.progress(line),
        });
        if (built.code !== 0 || !existsSync(binary)) {
          throw new Error(`SubVerso's extractor did not build for ${name}: ${tail(built.stderr || built.stdout, 300) || 'no output'}`);
        }
        return { binary, dir };
      })().finally(() => extractorBuilds.delete(dir)));
    }
    return extractorBuilds.get(dir);
  }

  /** The source roots Lake sets up for the project (`LEAN_SRC_PATH`), for naming modules. */
  async function sourceRoots(root, toolchain, job) {
    const result = await untrusted(toolchain.lake, ['env', 'printenv', 'LEAN_SRC_PATH'], { cwd: root, toolchain, writable: [job.dir] });
    return result.code === 0 ? result.stdout.trim().split('\n').pop() : '';
  }

  async function extract(root, file, context, job) {
    const key = fileKey(job.repo, job.sha, file.repoPath);
    fileStates.set(key, { state: 'running' });
    const output = path.join(context.workDir, `${sha256(file.repoPath)}.json`);
    try {
      const source = readFileSync(path.join(root, file.path), 'utf8');
      // The extractor runs under `lake env`, which gives it the project's modules.
      let args = ['env', context.extractor.binary];
      let cwd = root;
      let moduleName = moduleNameFor(root, context.srcPath, file.path);
      if (!moduleName) {
        // A file outside the project's libraries (a script, a test): elaborated on its own, from
        // its directory, against the project's built modules.
        moduleName = path.basename(file.path, '.lean');
        if (!/^[A-Za-z_][A-Za-z0-9_']*$/.test(moduleName)) throw new Error('This file is not part of a library of its Lake project');
        cwd = path.dirname(path.join(root, file.path));
        args = ['-d', root, 'env', 'env', '-u', 'LEAN_SRC_PATH', context.extractor.binary];
      }
      const result = await untrusted(context.toolchain.lake, [...args, moduleName, output], {
        cwd, toolchain: context.toolchain, readable: [context.extractor.dir], writable: [job.dir, context.workDir], timeoutMs: EXTRACT_TIMEOUT_MS,
      });
      if (result.code !== 0) throw new Error(`Lean could not process the file: ${tail(result.stderr || result.stdout, 400) || `exit ${result.code}`}`);
      const data = convertModule(JSON.parse(readFileSync(output, 'utf8')), source);
      const target = dataFile(job.repo, job.sha, file.repoPath);
      mkdirSync(path.dirname(target), { recursive: true });
      writeFileSync(target, JSON.stringify({ ...data, hash: sha256(source), lean: context.name }));
      fileStates.delete(key);
    } catch (error) {
      fileStates.set(key, { state: 'error', error: error.message });
      log(`  ${file.repoPath}: ${error.message}`);
    } finally {
      rmSync(output, { force: true });
      job.done += 1;
    }
  }

  async function runJob(job) {
    const dir = await ensureRepo(job);
    job.dir = realOrSame(dir);
    await checkout(dir, job);
    // Files grouped by the Lake project they belong to (usually one, at the repository root).
    const groups = new Map();
    for (const repoPath of job.paths) {
      const rootDir = existsSync(path.join(dir, repoPath)) ? lakeRootFor(dir, repoPath) : null;
      if (rootDir === null) {
        fileStates.set(fileKey(job.repo, job.sha, repoPath), {
          state: 'error',
          error: existsSync(path.join(dir, repoPath)) ? 'This file is not inside a Lake project' : 'This file does not exist at that commit',
        });
        job.done += 1;
        continue;
      }
      if (!groups.has(rootDir)) groups.set(rootDir, []);
      groups.get(rootDir).push({ repoPath, path: rootDir ? repoPath.slice(rootDir.length + 1) : repoPath });
    }
    const workDir = path.join(madeDir(path.join(cacheDir, 'work')), randomBytes(6).toString('hex'));
    mkdirSync(workDir, { recursive: true });
    try {
      for (const [rootDir, files] of groups) {
        const root = path.join(job.dir, rootDir);
        job.phase = 'preparing';
        const toolchain = await resolveToolchain(root, job);
        await ensureDependencies(root, rootDir, toolchain, job);
        await buildImports(root, files.map((file) => file.path), toolchain, job);
        const extractor = await ensureExtractor(root, toolchain, job);
        const context = { extractor, toolchain, workDir, name: toolchainOf(root), srcPath: await sourceRoots(root, toolchain, job) };
        job.phase = 'elaborating';
        job.say(`Elaborating ${files.length} file${files.length === 1 ? '' : 's'}`);
        let next = 0;
        const worker = async () => { while (next < files.length) await extract(root, files[next++], context, job); };
        await Promise.all(Array.from({ length: Math.min(poolSize, files.length) }, worker));
      }
    } finally {
      rmSync(workDir, { recursive: true, force: true });
    }
  }

  // --- What the extension asks for -----------------------------------------------------------

  /** Start elaborating files of a commit (those not done already). Returns the commit's status. */
  function start({ repo, sha, pr, paths }) {
    const todo = paths.filter((file) => {
      const state = fileStates.get(fileKey(repo, sha, file));
      return !existsSync(dataFile(repo, sha, file)) && !(state && (state.state === 'queued' || state.state === 'running'));
    });
    if (todo.length) {
      const job = {
        repo, sha, pr, paths: todo, phase: 'queued', message: 'Waiting for the previous run', notes: [], done: 0, error: null, finished: false,
        say(message) { this.message = message; log(`${repo}@${sha.slice(0, 7)}: ${message}`); },
        progress(line) { this.detail = line.slice(0, 200); },
        note(message) { this.notes.push(message); log(`${repo}@${sha.slice(0, 7)}: ${message}`); },
      };
      todo.forEach((file) => fileStates.set(fileKey(repo, sha, file), { state: 'queued' }));
      latestJob.set(`${repo}@${sha}`, job);
      const previous = repoQueues.get(repo) || Promise.resolve();
      const current = previous.then(() => runJob(job)).then(
        () => { job.phase = 'done'; job.say(`Done (${todo.length} file${todo.length === 1 ? '' : 's'})`); },
        (error) => {
          job.phase = 'error';
          job.error = error.message;
          log(`${repo}@${sha.slice(0, 7)}: ${error.message}`);
          for (const file of todo) {
            const key = fileKey(repo, sha, file);
            const state = fileStates.get(key);
            if (state && state.state !== 'error') fileStates.set(key, { state: 'error', error: error.message });
          }
        },
      ).finally(() => { job.finished = true; });
      repoQueues.set(repo, current);
      job.promise = current;
    }
    return status(repo, sha);
  }

  function status(repo, sha) {
    const job = latestJob.get(`${repo}@${sha}`);
    if (!job) return { state: 'idle' };
    return {
      state: job.finished ? (job.error ? 'error' : 'done') : 'pending',
      phase: job.phase, message: job.message, detail: job.detail, done: job.done, total: job.paths.length,
      error: job.error || undefined, notes: job.notes.length ? job.notes : undefined,
    };
  }

  function fileState(repo, sha, file) {
    if (existsSync(dataFile(repo, sha, file))) return { state: 'ready' };
    const state = fileStates.get(fileKey(repo, sha, file));
    if (!state) return { state: 'missing' };
    if (state.state === 'error') return { state: 'error', error: state.error };
    return { ...status(repo, sha), state: 'pending' };
  }

  const readData = (repo, sha, file) => readFileSync(dataFile(repo, sha, file), 'utf8');

  /** Answer one request: `{status, body}` with `body` a JSON string. */
  function handle(method, url, body) {
    const json = (status, value) => ({ status, body: typeof value === 'string' ? value : JSON.stringify(value) });
    const { pathname, searchParams } = new URL(url, 'http://127.0.0.1');
    const request = body || {};
    if (method === 'GET' && pathname === '/status') {
      return json(200, { ok: true, name: 'lean-lens-helper', version: HELPER_VERSION, format: DATA_FORMAT_VERSION, allow: config.allow, sandbox: sandboxState });
    }
    if (method === 'POST' && pathname === '/allow') {
      if (!isRepo(request.repo)) return json(400, { error: 'Bad repository name' });
      allow(request.repo);
      return json(200, { ok: true, allow: config.allow });
    }
    const repo = method === 'GET' ? searchParams.get('repo') : request.repo;
    const sha = method === 'GET' ? searchParams.get('sha') : request.sha;
    if (!isRepo(repo) || !isSha(sha)) return json(400, { error: 'Bad repository or commit' });
    if (!config.allow.includes(repo)) return json(403, { state: 'not_allowed', repo });
    if (method === 'GET' && pathname === '/job') return json(200, status(repo, sha));
    if (method === 'POST' && pathname === '/run') {
      const paths = Array.isArray(request.paths) ? [...new Set(request.paths)] : [];
      if (!paths.length || paths.length > 500 || !paths.every(isLeanPath)) return json(400, { error: 'Bad file list' });
      const pr = Number.isInteger(Number(request.pr)) && Number(request.pr) > 0 ? Number(request.pr) : null;
      return json(200, start({ repo, sha, pr, paths }));
    }
    if (method === 'POST' && pathname === '/file') {
      if (!isLeanPath(request.path)) return json(400, { error: 'Bad file path' });
      const state = fileState(repo, sha, request.path);
      if (state.state !== 'ready') return json(200, state);
      return json(200, `{"state":"ready","data":${readData(repo, sha, request.path)}}`);
    }
    return json(404, { error: 'Unknown request' });
  }

  /** How a project's code is confined: 'seatbelt', 'none' (this system can't) or 'off'. */
  const sandbox = () => sandboxKind.then(() => sandboxState);

  return { cacheDir, config, allow, link, start, status, fileState, readData, handle, poolSize, sandbox };
}

// ---------------------------------------------------------------------------------------------
// The local web server.

/** Whether a request may be answered: from this machine's extension, with the helper's token. */
export function authorized(headers, port, token) {
  const host = headers.host || '';
  if (host !== `127.0.0.1:${port}` && host !== `localhost:${port}`) return false; // DNS rebinding
  const origin = headers.origin;
  if (origin && !/^(?:chrome|moz)-extension:\/\//.test(origin)) return false; // a web page
  const given = Buffer.from(String(headers['x-lean-lens-token'] || ''));
  const expected = Buffer.from(token);
  return given.length === expected.length && timingSafeEqual(given, expected);
}

export function serve(helper, port = DEFAULT_PORT) {
  const server = http.createServer((request, response) => {
    const origin = request.headers.origin;
    const fromExtension = origin && /^(?:chrome|moz)-extension:\/\//.test(origin);
    const send = (status, body) => {
      response.writeHead(status, {
        'Content-Type': 'application/json; charset=utf-8',
        'Cache-Control': 'no-store',
        ...(fromExtension ? { 'Access-Control-Allow-Origin': origin, Vary: 'Origin' } : {}),
      });
      response.end(body);
    };
    if (request.method === 'OPTIONS') {
      response.writeHead(fromExtension ? 204 : 403, fromExtension ? {
        'Access-Control-Allow-Origin': origin,
        'Access-Control-Allow-Methods': 'GET, POST',
        'Access-Control-Allow-Headers': 'content-type, x-lean-lens-token',
        'Access-Control-Max-Age': '600',
        Vary: 'Origin',
      } : {});
      response.end();
      return;
    }
    if (!authorized(request.headers, port, helper.config.token)) {
      send(401, JSON.stringify({ error: 'Not authorized: check the helper token in the extension options' }));
      return;
    }
    const chunks = [];
    let size = 0;
    request.on('data', (chunk) => {
      size += chunk.length;
      if (size > MAX_BODY_BYTES) request.destroy(); else chunks.push(chunk);
    });
    request.on('end', () => {
      let body = null;
      try {
        if (chunks.length) body = JSON.parse(Buffer.concat(chunks).toString('utf8'));
      } catch {
        send(400, JSON.stringify({ error: 'The request body is not JSON' }));
        return;
      }
      try {
        const result = helper.handle(request.method, request.url, body);
        send(result.status, result.body);
      } catch (error) {
        send(500, JSON.stringify({ error: error.message }));
      }
    });
  });
  return new Promise((resolve, reject) => {
    server.once('error', reject);
    server.listen(port, '127.0.0.1', () => resolve(server));
  });
}

// ---------------------------------------------------------------------------------------------
// Command line.

const USAGE = `Lean Lens helper: real Lean hovers and proof states for the extension.

  node lean-lens-helper.mjs [options]                  start the helper
  node lean-lens-helper.mjs run --repo owner/repo --sha COMMIT [--pr N] File.lean …
                                                       elaborate files once, without the extension

Options
  --port N                  port on 127.0.0.1 (default ${DEFAULT_PORT})
  --allow owner/repo        allow a repository (remembered; can be repeated)
  --link owner/repo=PATH    start from your existing checkout of a repository, so its commits
                            and its build are reused instead of downloaded (remembered)
  --cache DIR               where clones, builds and results are kept
  --jobs N                  files elaborated at once
  --subverso URL-or-PATH    where to get SubVerso (default ${DEFAULT_SUBVERSO})
  --subverso-rev REV        SubVerso revision to build
  --clone-base URL          where repositories are cloned from (default ${DEFAULT_CLONE_BASE})
  --no-sandbox              run a project's code with your own permissions and environment
`;

async function main() {
  const { values, positionals } = parseArgs({
    allowPositionals: true,
    options: {
      port: { type: 'string' }, cache: { type: 'string' }, jobs: { type: 'string' },
      allow: { type: 'string', multiple: true }, link: { type: 'string', multiple: true },
      subverso: { type: 'string' }, 'subverso-rev': { type: 'string' }, 'clone-base': { type: 'string' },
      repo: { type: 'string' }, sha: { type: 'string' }, pr: { type: 'string' }, 'no-sandbox': { type: 'boolean' },
      help: { type: 'boolean', short: 'h' },
    },
  });
  if (values.help) { console.log(USAGE); return; }
  const helper = createHelper({
    cacheDir: values.cache, jobs: values.jobs, subverso: values.subverso, subversoRev: values['subverso-rev'],
    cloneBase: values['clone-base'], sandbox: !values['no-sandbox'],
  });
  const sandboxLine = {
    seatbelt: "on: the project's code runs without network access and cannot read or change your files",
    none: 'not available on this system: Lean runs with your permissions',
    off: 'off (--no-sandbox): Lean runs with your permissions',
  }[await helper.sandbox()];
  for (const entry of values.link || []) {
    const split = entry.indexOf('=');
    if (split < 1) throw new Error(`--link takes owner/repo=PATH, not ${entry}`);
    helper.link(entry.slice(0, split), entry.slice(split + 1));
  }
  for (const repo of values.allow || []) helper.allow(repo);

  if (positionals[0] === 'run') {
    const paths = positionals.slice(1);
    if (!isRepo(values.repo) || !isSha(values.sha) || !paths.length || !paths.every(isLeanPath)) {
      throw new Error('run needs --repo owner/repo, --sha with a full commit hash, and Lean files');
    }
    helper.allow(values.repo);
    console.log(`Sandbox ${sandboxLine}`);
    helper.start({ repo: values.repo, sha: values.sha, pr: Number(values.pr) || null, paths });
    await new Promise((resolve) => {
      const poll = setInterval(() => {
        const state = helper.status(values.repo, values.sha).state;
        if (state === 'done' || state === 'error') { clearInterval(poll); resolve(); }
      }, 300);
    });
    let failed = helper.status(values.repo, values.sha).state === 'error';
    for (const file of paths) {
      const state = helper.fileState(values.repo, values.sha, file);
      console.log(`${file}: ${state.state}${state.error ? ` (${state.error})` : ''}`);
      if (state.state !== 'ready') failed = true;
    }
    if (failed) process.exitCode = 1;
    return;
  }

  const port = Number(values.port) || DEFAULT_PORT;
  await serve(helper, port);
  console.log(`Lean Lens helper is running.

  Address  http://127.0.0.1:${port}
  Token    ${helper.config.token}

Paste both into the extension's options, under "Real Lean".
Sandbox ${sandboxLine}.
Allowed repositories: ${helper.config.allow.length ? helper.config.allow.join(', ') : 'none yet (allow one from the extension, or with --allow owner/repo)'}
Kept in: ${helper.cacheDir}
`);
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  main().catch((error) => {
    console.error(error.message);
    process.exitCode = 1;
  });
}
