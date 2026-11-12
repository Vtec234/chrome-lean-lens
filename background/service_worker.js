/**
 * Background service worker for Lean Lens.
 * Coordinates definition queries across Loogle, the local companion server, and caches.
 */

// Shared binder parsing (also used by the content script).
if (typeof importScripts === 'function') {
  try { importScripts('../content/binder_context.js', '../content/pr_scanner.js'); } catch (err) { /* lookups still work without them */ }
}

const SETTINGS_KEY = "lean_lens_settings";
const LEGACY_SETTINGS_KEY = "verso_settings";

const DEFAULT_SETTINGS = {
  enabled: true,
  hoverDelay: 250,
  enablePRScanner: true,
  enableBuiltins: true,
  enableLoogle: true,
  enableLocalVerso: false,
  localVersoUrl: "http://127.0.0.1:8000",
  theme: "auto"
};

// In-memory cache for speed during active review session
const memoryCache = new Map();
let queryStats = { totalQueries: 0, cacheHits: 0, loogleHits: 0, localHits: 0 };

/**
 * Get stored settings merged with defaults.
 */
async function getSettings() {
  return new Promise((resolve) => {
    chrome.storage.local.get([SETTINGS_KEY, LEGACY_SETTINGS_KEY], (res) => {
      let saved = res[SETTINGS_KEY];
      // One-time migration from the extension's former name ("Verso").
      if (!saved && res[LEGACY_SETTINGS_KEY]) {
        saved = res[LEGACY_SETTINGS_KEY];
        chrome.storage.local.set({ [SETTINGS_KEY]: saved }, () => chrome.storage.local.remove(LEGACY_SETTINGS_KEY));
      }
      resolve(Object.assign({}, DEFAULT_SETTINGS, saved || {}));
    });
  });
}

/**
 * Determine declaration kind from signature or name.
 */
function inferKind(name, type, doc) {
  if (!name) return "def";
  const lowerName = name.toLowerCase();
  const lowerType = (type || "").toLowerCase();

  if (lowerName.includes("tactic") || lowerType.includes("tacticm")) return "tactic";
  if (lowerType.startsWith("class ") || lowerType.includes(" : class")) return "class";
  if (lowerType.startsWith("structure ")) return "structure";
  if (lowerType.startsWith("inductive ")) return "inductive";
  if (lowerType.includes(" : prop") || lowerType.includes("→ prop") || lowerName.endsWith("_iff") || lowerName.startsWith("theorem_")) {
    return "theorem";
  }
  return "def";
}

/**
 * Construct Mathlib4 docs deep-link URL.
 */
function getMathlibDocsUrl(moduleName, declName) {
  if (!moduleName || !declName) {
    return "https://leanprover-community.github.io/mathlib4_docs/";
  }
  const modPath = moduleName.replace(/\./g, "/");
  return `https://leanprover-community.github.io/mathlib4_docs/${modPath}.html#${encodeURIComponent(declName)}`;
}

/**
 * Query the local companion server if enabled.
 */
async function queryLocalVerso(token, localUrl) {
  try {
    const url = new URL("/lookup", localUrl);
    url.searchParams.set("name", token);

    const controller = new AbortController();
    const timeout = setTimeout(() => controller.abort(), 1200);

    const response = await fetch(url.toString(), {
      method: "GET",
      signal: controller.signal,
      headers: { "Accept": "application/json" }
    });
    clearTimeout(timeout);

    if (!response.ok) return null;
    const json = await response.json();
    if (json && json.name) {
      return {
        name: json.name,
        kind: json.kind || inferKind(json.name, json.type, json.doc),
        typeSignature: json.type || json.typeSignature || "",
        docstring: json.doc || json.docstring || "",
        module: json.module || "LocalProject",
        source: "local_verso",
        sourceUrl: json.sourceUrl || `${localUrl}/doc#${encodeURIComponent(json.name)}`
      };
    }
  } catch (err) {
    // Local server offline or unreachable; fall through quietly
  }
  return null;
}

/**
 * Query Loogle API raw endpoint.
 */
// Raw Loogle responses for this worker's lifetime: hovers and scope checks repeat queries.
const rawQueryCache = new Map();

async function queryLoogleRaw(queryStr) {
  if (rawQueryCache.has(queryStr)) return rawQueryCache.get(queryStr);
  const result = await queryLoogleRawUncached(queryStr);
  if (result !== undefined) {
    if (rawQueryCache.size > 1000) rawQueryCache.delete(rawQueryCache.keys().next().value);
    rawQueryCache.set(queryStr, result);
  }
  return result;
}

/** Returns hits, null for "no such name / no hits", or undefined on a network failure (not cached). */
async function queryLoogleRawUncached(queryStr) {
  try {
    const loogleUrl = `https://loogle.lean-lang.org/json?q=${encodeURIComponent(queryStr)}`;
    const controller = new AbortController();
    const timeout = setTimeout(() => controller.abort(), 3500);

    const response = await fetch(loogleUrl, {
      method: "GET",
      signal: controller.signal,
      headers: { "Accept": "application/json" }
    });
    clearTimeout(timeout);

    if (!response.ok) return undefined;
    const data = await response.json();
    if (data && Array.isArray(data.hits) && data.hits.length > 0) {
      return data.hits;
    }
    return null;
  } catch (err) {
    return undefined; // network error / timeout: let callers move on, don't cache
  }
}

const CACHE_VERSION = "v4";

/**
 * True if `name` ends with the dotted segments of `token`.
 * Qualifier segments compare case-insensitively, because dot notation writes the
 * receiver namespace in lowerCamelCase (`hl.sortedLE.pairwise` → `List.SortedLE.pairwise`).
 * The last segment must match exactly.
 */
function nameMatchesToken(name, token) {
  const nameSegs = name.split('.');
  const tokenSegs = token.split('.');
  if (tokenSegs.length > nameSegs.length) return false;
  const offset = nameSegs.length - tokenSegs.length;
  for (let i = 0; i < tokenSegs.length; i++) {
    const a = nameSegs[offset + i];
    const b = tokenSegs[i];
    const isLast = i === tokenSegs.length - 1;
    if (isLast ? a !== b : a.toLowerCase() !== b.toLowerCase()) return false;
  }
  return true;
}

/**
 * Choose the Loogle hit for a hovered token.
 * Returns { hit } for a confident match, { candidates } when the text alone can't decide
 * (we don't know the receiver's type), or null when nothing in `hits` fits.
 * Never falls back to an arbitrary hit: a wrong lemma is worse than no answer.
 */
function selectLoogleHit(hits, token, shortName) {
  if (!Array.isArray(hits) || hits.length === 0 || !token) return null;
  const last = shortName || token.split('.').pop();

  if (token.includes('.')) {
    const matches = hits.filter(h => h.name && nameMatchesToken(h.name, token));
    if (matches.length > 0) {
      const exact = matches.find(h => h.name === token);
      if (exact) return { hit: exact };
      if (matches.length === 1) return { hit: matches[0] };
      // Several namespaces end the same way (e.g. `Nonempty.mono` in Set and Finset):
      // an exact-case suffix can still single one out, otherwise we can't tell.
      const exactCase = matches.filter(h => h.name.endsWith('.' + token));
      if (exactCase.length === 1) return { hit: exactCase[0] };
      return { candidates: matches };
    }
    // Qualifier didn't match anything: we can only list what the last segment might be.
    const candidates = hits.filter(h => h.name && nameMatchesToken(h.name, last));
    return candidates.length > 0 ? { candidates } : null;
  }

  // Bare token: exact root declaration wins, then a unique suffix match.
  const exact = hits.find(h => h.name === token);
  if (exact) return { hit: exact };
  const matches = hits.filter(h => h.name && nameMatchesToken(h.name, token));
  if (matches.length === 1) return { hit: matches[0] };
  if (matches.length > 1) return { candidates: matches };
  return null;
}

const MAX_CANDIDATES_SHOWN = 8;

function buildAmbiguousResult(token, candidates) {
  const label = token.split('.').pop();
  const shown = candidates.slice(0, MAX_CANDIDATES_SHOWN);
  const more = candidates.length - shown.length;
  const lines = shown.map(h => `- \`${h.name}\``);
  if (more > 0) lines.push(`- …and ${more} more`);
  return {
    name: label,
    kind: "ambiguous",
    typeSignature: `-- ${candidates.length} possible declaration${candidates.length === 1 ? "" : "s"} named ${label}`,
    docstring:
      `Couldn't tell which \`${label}\` this is from the text alone: it depends on the type of the receiver, which only Lean knows. Possible matches:\n\n` +
      lines.join('\n'),
    module: "",
    source: "loogle",
    ambiguous: true,
    sourceUrl: `https://leanprover-community.github.io/mathlib4_docs/find/?pattern=${encodeURIComponent(label)}#doc`
  };
}

function hitToResult(hit) {
  const kind = inferKind(hit.name, hit.type, hit.doc);
  const moduleName = hit.module || "";
  return {
    name: hit.name,
    kind: kind,
    typeSignature: hit.type || `${kind} ${hit.name}`,
    docstring: hit.doc || "",
    module: moduleName,
    source: "loogle",
    sourceUrl: getMathlibDocsUrl(moduleName, hit.name)
  };
}

/**
 * Smart Loogle Query with automatic namespace resolution and substring search.
 * Resolves opened namespaces (e.g. ZeroAtFilter -> Filter.ZeroAtFilter) and dot notation.
 */
async function queryLoogle(token, subToken) {
  if (!token) return null;
  const shortName = subToken || (token.includes('.') ? token.split('.').pop() : token);

  // 1. Exact token, 2. substring search for the token, 3. substring search for the last segment.
  const candidateQueries = Array.from(new Set([token, `"${token}"`, `"${shortName}"`]));

  let ambiguous = null;
  for (const q of candidateQueries) {
    const hits = await queryLoogleRaw(q);
    const picked = selectLoogleHit(hits, token, shortName);
    if (!picked) continue;
    if (picked.hit) return hitToResult(picked.hit);
    if (!ambiguous) ambiguous = picked.candidates;
  }

  return ambiguous ? buildAmbiguousResult(token, ambiguous) : null;
}

// ---------------------------------------------------------------------------
// Tactic docs: Mathlib's tactic reference page, parsed once and cached.
// ---------------------------------------------------------------------------

const TACTIC_DOCS_URL = "https://leanprover-community.github.io/mathlib4_docs/tactics.html";
const TACTIC_CACHE_KEY = "tactic_docs_v1";
const TACTIC_CACHE_MS = 1000 * 60 * 60 * 24 * 7;
let tacticDocsPromise = null;

function decodeEntities(s) {
  return s
    .replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&quot;/g, '"')
    .replace(/&#39;|&#x27;/g, "'").replace(/&nbsp;/g, ' ')
    .replace(/&#(\d+);/g, (_, n) => String.fromCodePoint(+n))
    .replace(/&#x([0-9a-f]+);/gi, (_, n) => String.fromCodePoint(parseInt(n, 16)))
    .replace(/&amp;/g, '&');
}

/** doc-gen4 docstring HTML → the small Markdown subset the tooltip renders. */
function docHtmlToMarkdown(html) {
  const stripTags = (t) => t.replace(/<[^>]+>/g, '');
  let md = html
    .replace(/<pre[^>]*>\s*<code[^>]*>([\s\S]*?)<\/code>\s*<\/pre>/g, (_, code) => `\n\n\`\`\`lean\n${stripTags(code).trim()}\n\`\`\`\n\n`)
    .replace(/<code[^>]*>([\s\S]*?)<\/code>/g, (_, code) => '`' + stripTags(code) + '`')
    .replace(/<(strong|b)>([\s\S]*?)<\/\1>/g, '**$2**')
    .replace(/<(em|i)>([\s\S]*?)<\/\1>/g, '*$2*')
    .replace(/<li[^>]*>/g, '\n- ').replace(/<\/li>/g, '')
    .replace(/<\/?(ul|ol)[^>]*>/g, '\n')
    .replace(/<br\s*\/?>/g, '\n')
    .replace(/<\/?p[^>]*>/g, '\n\n');
  md = decodeEntities(stripTags(md));
  return md.replace(/[ \t]+\n/g, '\n').replace(/\n{3,}/g, '\n\n').trim();
}

/** Parse tactics.html into { name: { doc, module, anchor } } (first entry per name wins). */
function parseTacticDocs(html) {
  const docs = {};
  const re = /<div id="([^"]+)"><div id="userName-[^"]*"><h2>([\s\S]*?)<\/h2>([\s\S]*?)<dl>([\s\S]*?)<\/dl>/g;
  let m;
  while ((m = re.exec(html)) !== null) {
    const name = decodeEntities(m[2].replace(/<[^>]+>/g, '')).trim();
    if (!/^[A-Za-z_][\w'!?]*$/.test(name) || docs[name]) continue;
    const mod = (m[4].match(/Defined in module:<\/dt><dd><a[^>]*>([^<]+)<\/a>/) || [])[1] || '';
    docs[name] = { doc: docHtmlToMarkdown(m[3]), module: mod.trim(), anchor: decodeEntities(m[1]) };
  }
  return docs;
}

function getTacticDocs() {
  if (!tacticDocsPromise) {
    tacticDocsPromise = (async () => {
      const cached = await new Promise((res) => {
        try { chrome.storage.local.get([TACTIC_CACHE_KEY], (r) => res(r && r[TACTIC_CACHE_KEY])); } catch (err) { res(null); }
      });
      if (cached && Date.now() - cached.timestamp < TACTIC_CACHE_MS) return cached.docs;
      const html = await fetchText(TACTIC_DOCS_URL, 15000);
      if (!html) return cached ? cached.docs : {};
      const docs = parseTacticDocs(html);
      try { chrome.storage.local.set({ [TACTIC_CACHE_KEY]: { timestamp: Date.now(), docs } }); } catch (err) { /* ignore */ }
      return docs;
    })().catch(() => { tacticDocsPromise = null; return {}; });
  }
  return tacticDocsPromise;
}

async function lookupTactic(token) {
  if (!token || token.includes('.')) return null;
  const docs = await getTacticDocs();
  const entry = docs && docs[token];
  if (!entry) return null;
  return {
    name: token,
    kind: 'tactic',
    typeSignature: `tactic ${token}`,
    docstring: entry.doc,
    module: entry.module,
    source: 'loogle',
    sourceUrl: `${TACTIC_DOCS_URL}#${encodeURIComponent(entry.anchor)}`
  };
}

// ---------------------------------------------------------------------------
// File scope: which namespaces a bare identifier can resolve in at a given line.
// ---------------------------------------------------------------------------

const SCOPE_DECL = /^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|public|noncomputable|scoped|partial|nonrec|unsafe|meta)\s+)*(theorem|lemma|def|abbrev|instance|opaque|example|structure|class|inductive)\b\s*([^\s(:{\[⦃]*)/;

/** Remove `--` line comments and (nested) `/- … -/` block comments, carrying depth across lines. */
function stripLeanComments(line, state) {
  let out = '';
  for (let i = 0; i < line.length; i++) {
    if (line.startsWith('/-', i)) { state.depth++; i++; continue; }
    if (state.depth > 0) {
      if (line.startsWith('-/', i)) { state.depth--; i++; }
      continue;
    }
    if (line.startsWith('--', i)) break;
    out += line[i];
  }
  return out;
}

/** Parse the body of an `open` command into [{ ns, only }] (scoped/renaming opens give no names). */
function parseOpen(body) {
  const result = [];
  const re = /([^\s()]+)(?:\s*\(([^)]*)\))?/g;
  let m;
  while ((m = re.exec(body)) !== null) {
    const word = m[1];
    if (word === 'scoped') return result; // only notations/instances, no names
    if (word === 'hiding' || word === 'renaming' || word === '→' || word === 'in') break;
    result.push({ ns: word, only: m[2] ? m[2].trim().split(/\s+/) : null });
  }
  return result;
}

function prefixesOf(ns) {
  const segs = ns.split('.').filter(Boolean);
  const out = [];
  for (let k = segs.length; k > 0; k--) out.push(segs.slice(0, k).join('.'));
  return out;
}

/**
 * Namespaces in scope at 1-based `line` of a Lean file, most specific first:
 * the declaration's own namespace, the current `namespace` chain, then `open`s
 * (innermost scope and latest `open` first). Each entry: { ns, only }.
 */
function scopeAt(text, line) {
  const { frames, declNs, declOpenIn } = walkScope(text, line);
  const ordered = [];
  const seen = new Set();
  const add = (ns, only = null, origin = 'open') => {
    const key = ns + '|' + (only ? only.join(',') : '');
    if (seen.has(key)) return;
    seen.add(key);
    ordered.push({ ns, only, origin });
  };
  if (declNs) prefixesOf(declNs).forEach(ns => add(ns, null, 'namespace'));
  const cur = frames.filter(f => f.kind === 'namespace').map(f => f.name).join('.');
  if (cur) prefixesOf(cur).forEach(ns => add(ns, null, 'namespace'));
  // Later `open` commands first; names within one command keep source order.
  declOpenIn.forEach(o => add(o.ns, o.only));
  for (let f = frames.length - 1; f >= 0; f--) {
    frames[f].opens.slice().reverse().forEach(group => group.forEach(o => add(o.ns, o.only)));
  }
  return ordered;
}

/**
 * `variable` commands still in scope at 1-based `line`, as [{ text, line }], outermost first.
 */
function variablesAt(text, line) {
  const { frames } = walkScope(text, line);
  return frames.flatMap(f => f.variables);
}

/** Walk a Lean file up to `line`, tracking namespace/section frames, opens and variables. */
function walkScope(text, line) {
  const lines = text.split('\n');
  const frames = [{ kind: 'root', name: '', opens: [], variables: [] }];
  const state = { depth: 0 };
  let pendingOpenIn = [];
  let declOpenIn = [];
  let declNs = null;
  let openVariable = null; // `variable` command whose indented continuation lines we're reading

  const upto = Math.min(line, lines.length);
  for (let i = 0; i < upto; i++) {
    const raw = stripLeanComments(lines[i], state);
    let t = raw.trim();
    if (openVariable && t && /^\s/.test(raw)) { openVariable.text += '\n' + raw; continue; }
    openVariable = null;
    if (!t) continue;
    if (/^variable\b/.test(t)) {
      openVariable = { text: t, line: i + 1 };
      frames[frames.length - 1].variables.push(openVariable);
      continue;
    }
    let m;
    const openIn = t.match(/^open\s+(.*?)\s+in\b\s*(.*)$/);
    if (openIn) {
      pendingOpenIn = parseOpen(openIn[1]);
      t = openIn[2].trim();
      if (!t) continue;
    }
    if ((m = t.match(/^namespace\s+(\S+)/))) {
      frames.push({ kind: 'namespace', name: m[1], opens: [], variables: [] });
    } else if (/^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|public|private)\s+)*section\b/.test(t)) {
      frames.push({ kind: 'section', name: '', opens: [], variables: [] });
    } else if (/^end\b/.test(t)) {
      if (frames.length > 1) frames.pop();
    } else if ((m = t.match(/^open\s+(.*)$/))) {
      frames[frames.length - 1].opens.push(parseOpen(m[1]));
    } else if ((m = t.match(SCOPE_DECL))) {
      const cur = frames.filter(f => f.kind === 'namespace').map(f => f.name).join('.');
      let name = m[2] || '';
      let abs = false;
      if (name.startsWith('_root_.')) { name = name.slice(7); abs = true; }
      const parent = name.includes('.') ? name.slice(0, name.lastIndexOf('.')) : '';
      declNs = parent ? (abs || !cur ? parent : `${cur}.${parent}`) : null;
      if (m[1] === 'structure' || m[1] === 'class' || m[1] === 'inductive') {
        declNs = abs || !cur ? name : `${cur}.${name}`;
      }
      declOpenIn = pendingOpenIn;
      pendingOpenIn = [];
    }
  }
  return { frames, declNs, declOpenIn };
}

/** A `variable`-declared name at `fileRef.line`, as tooltip data, or null. */
async function lookupFileVariable(token, fileRef) {
  const bc = self.VersoBinderContext;
  if (!bc || !fileRef || !fileRef.line) return null;
  const text = await getFileText(fileRef);
  if (!text) return null;
  const vars = variablesAt(text, fileRef.line);
  // Later `variable` commands shadow earlier ones.
  for (let k = vars.length - 1; k >= 0; k--) {
    const type = bc.findBinderType(token, vars[k].text);
    if (type) {
      return {
        name: token, kind: 'variable', source: 'local_var', declaredAt: vars[k].line, rawType: type,
        typeSignature: `${token} : ${type}`,
        docstring: `Declared with \`variable\` at line ${vars[k].line} of this file.`
      };
    }
  }
  return null;
}

const fileTextCache = new Map(); // key → Promise<string|null>
const prRevisionCache = new Map(); // owner/repo#pr → Promise<{head, base}|null>

async function fetchText(url, ms = 5000, init = {}) {
  const controller = new AbortController();
  const timer = setTimeout(() => controller.abort(), ms);
  try {
    const res = await fetch(url, Object.assign({ signal: controller.signal }, init));
    return res.ok ? await res.text() : null;
  } catch (err) {
    return null;
  } finally {
    clearTimeout(timer);
  }
}

function getPrRevision(owner, repo, pr) {
  const key = `${owner}/${repo}#${pr}`;
  if (!prRevisionCache.has(key)) {
    prRevisionCache.set(key, fetchText(`https://api.github.com/repos/${owner}/${repo}/pulls/${pr}`).then(t => {
      if (!t) return null;
      const j = JSON.parse(t);
      return { head: j.head && j.head.sha, base: j.base && j.base.sha };
    }).catch(() => null));
  }
  return prRevisionCache.get(key);
}

async function getFileText(fileRef) {
  let sha = fileRef.sha;
  if (!sha && fileRef.pr) {
    const rev = await getPrRevision(fileRef.owner, fileRef.repo, fileRef.pr);
    sha = rev && (fileRef.side === 'left' ? rev.base : rev.head);
  }
  if (!sha || !fileRef.path) return null;
  const key = `${fileRef.owner}/${fileRef.repo}@${sha}:${fileRef.path}`;
  if (!fileTextCache.has(key)) {
    if (fileTextCache.size > 300) fileTextCache.delete(fileTextCache.keys().next().value);
    const path = fileRef.path.split('/').map(encodeURIComponent).join('/');
    fileTextCache.set(key, fetchText(`https://raw.githubusercontent.com/${fileRef.owner}/${fileRef.repo}/${sha}/${path}`)
      // Private repositories: github.com's raw endpoint with the user's GitHub session.
      .then(t => t !== null ? t : fetchText(`https://github.com/${fileRef.owner}/${fileRef.repo}/raw/${sha}/${path}`, 8000, { credentials: 'include' })));
  }
  return fileTextCache.get(key);
}

/** Modules a Lean file imports (`import A.B`, `public import A.B`, `import all A`). */
function importsOf(text) {
  const out = [];
  const re = /^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.'«»]+)/gm;
  let m;
  while ((m = re.exec(text)) !== null) out.push(m[1]);
  return out;
}

/**
 * Declarations in a PR's Lean files, read from the files at the PR's commit rather than the
 * page (GitHub collapses large diffs). Outside Mathlib, also the project files they import,
 * following imports within the repository (Loogle only knows Mathlib).
 */
async function projectDeclarations({ owner, repo, pr, sha, paths }) {
  const scanner = self.LeanPRScanner;
  if (!scanner || !paths || !paths.length) return [];
  if (!sha && pr) {
    const rev = await getPrRevision(owner, repo, pr);
    sha = rev && rev.head;
  }
  if (!sha) return [];
  const isMathlib = /^leanprover-community\/mathlib4?$/i.test(`${owner}/${repo}`);
  const roots = new Set(paths.map(p => p.split('/')[0].replace(/\.lean$/, '')));
  const changed = new Set(paths);
  const queue = paths.filter(p => p.endsWith('.lean'));
  const seen = new Set();
  const decls = [];
  const limit = isMathlib ? queue.length : 120;
  while (queue.length && seen.size < limit) {
    const batch = [];
    while (queue.length && batch.length < 8 && seen.size + batch.length < limit) {
      const p = queue.shift();
      if (!seen.has(p) && !batch.includes(p)) batch.push(p);
    }
    batch.forEach(p => seen.add(p));
    const texts = await Promise.all(batch.map(p => getFileText({ owner, repo, sha, path: p })));
    batch.forEach((p, k) => {
      const text = texts[k];
      if (!text) return;
      for (const d of scanner.scanSource(text, p)) {
        decls.push(Object.assign(d, { inPR: changed.has(p), repo: `${owner}/${repo}`, sha }));
      }
      if (isMathlib) return;
      for (const mod of importsOf(text)) {
        if (!roots.has(mod.split('.')[0])) continue;
        const fp = mod.replace(/\./g, '/') + '.lean';
        if (!seen.has(fp) && !queue.includes(fp)) queue.push(fp);
      }
    });
  }
  return decls;
}

/** Does `name` exist? Returns the Loogle hit for it, or null. */
async function loogleExact(name) {
  const hits = await queryLoogleRaw(name);
  if (!hits) return null;
  let hit = hits.find(h => h.name === name);
  if (!hit) {
    const more = await queryLoogleRaw(`"${name}"`);
    hit = more && more.find(h => h.name === name);
  }
  return hit || { name, type: '', doc: '', module: '' };
}

/**
 * A root name that is really an `export`ed class field (`mul_zero` → `MulZeroClass.mul_zero`,
 * `star` → `Star.star`, `algebraMap` → `Algebra.algebraMap`). Loogle doesn't know the short name.
 * A class-field projection has a `[self : Class …]` binder.
 */
async function exportedClassField(token) {
  if (!/^[a-z][\w'!?]*$/.test(token)) return null;
  const isField = (h) => {
    const ns = h.name.slice(0, h.name.length - token.length - 1);
    return ns && h.type && h.type.includes(`[self : ${ns}`) && !h.name.startsWith('Lean.');
  };
  const guess = await loogleExact(`${token[0].toUpperCase()}${token.slice(1)}.${token}`);
  if (guess && isField(guess)) return guess;
  const hits = await queryLoogleRaw(`"${token}"`);
  return (hits || []).find(h => h.name.endsWith('.' + token) && isField(h)) || null;
}

/**
 * Resolve a bare identifier using the namespaces open at its line, as Lean would.
 * `contextText` (the enclosing declaration) breaks ties between several real candidates.
 */
async function resolveInScope(token, scope, contextText) {
  const candidates = [];
  const origin = new Map();
  for (const { ns, only, origin: o } of scope) {
    if (only && !only.includes(token)) continue;
    const name = `${ns}.${token}`;
    if (!origin.has(name)) origin.set(name, o);
    candidates.push(name);
  }
  candidates.push(token);
  const unique = Array.from(new Set(candidates)).slice(0, 12);
  const found = (await Promise.all(unique.map(loogleExact))).filter(h => h && h.type);
  if (!token.includes('.') && !found.some(h => h.name === token)) {
    // The root name may be an exported class field; treat it as the root candidate.
    const exported = await exportedClassField(token);
    if (exported) {
      const result = hitToResult(exported);
      result.docstring = `*\`${token}\` is exported from \`${exported.name}\`.*\n\n${result.docstring}`;
      return result;
    }
  }
  if (found.length === 0) return null;
  if (found.length === 1) return hitToResult(found[0]);
  const withNote = (hit, why) => {
    const result = hitToResult(hit);
    const others = found.filter(h => h !== hit).map(h => `\`${h.name}\``).join(', ');
    result.docstring = `*Also in scope here: ${others}. ${why}*\n\n${result.docstring}`;
    return result;
  };

  // A root name wins: Mathlib marks clashing namespaced names `protected`, and those
  // aren't reachable by `open` or by being inside the namespace.
  const root = found.find(h => h.name === token);
  if (root) return withNote(root, 'Picked the root declaration (namespaced ones with the same name are usually `protected`).');

  // The declaration's / current namespace beats `open`ed ones in practice
  // (Lean would try all and keep the one that typechecks).
  const own = found.filter(h => origin.get(h.name) === 'namespace');
  if (own.length >= 1 && own.length < found.length) {
    return withNote(own[0], 'Picked the one in the current namespace.');
  }

  // Several real candidates (Lean would pick by type). Prefer one whose namespace
  // is mentioned in the declaration, and say what else was in scope.
  const ctx = contextText || '';
  const mentioned = found.filter(h => {
    const ns = h.name.slice(0, h.name.length - token.length - 1);
    return ns && new RegExp(`(^|[^\\w.])${ns.replace(/\./g, '\\.')}(?![\\w])`).test(ctx);
  });
  if (mentioned.length === 1) return withNote(mentioned[0], 'Picked by the types used in this declaration.');
  return buildAmbiguousResult(token, found);
}

async function lookupInFileScope(token, fileRef, contextText, allowDotted = false) {
  if (!fileRef || !fileRef.line || (token.includes('.') && !allowDotted)) return null;
  const text = await getFileText(fileRef);
  if (!text) return null;
  // An empty scope still checks the root name (`mul_zero` in a file with no `open`).
  return resolveInScope(token, scopeAt(text, fileRef.line), contextText);
}

/**
 * Handle Token Lookup.
 */
/** Top-level binder groups of a Loogle signature (before ` : conclusion`): [{ names, type }]. */
function signatureBinders(sig) {
  const groups = [];
  const pairs = { '(': ')', '{': '}', '[': ']', '⦃': '⦄' };
  let i = 0;
  while (i < sig.length) {
    while (sig[i] === ' ') i++;
    const open = sig[i];
    if (!pairs[open]) break;
    let depth = 0, j = i;
    for (; j < sig.length; j++) {
      if ('({[⦃⟨'.includes(sig[j])) depth++;
      else if (')}]⦄⟩'.includes(sig[j])) { depth--; if (depth === 0) break; }
    }
    const group = sig.slice(i + 1, j);
    const colon = group.indexOf(' : ');
    if (colon !== -1) groups.push({ names: group.slice(0, colon).trim().split(/\s+/), type: group.slice(colon + 3).trim(), explicit: open === '(' });
    else groups.push({ names: [], type: group.trim(), explicit: false }); // anonymous instance `[Fact p]`
    i = j + 1;
  }
  return groups;
}

function replaceWord(text, name, value) {
  // Not inside a longer name or a field access `x.name`; after a range `a..name` it counts.
  const esc = name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  return text.replace(new RegExp(`(?<![\\w'\\u2080-\\u209C])(?<!(?:^|[^.])\\.)${esc}(?![\\w'\\u2080-\\u209C])`, 'g'), () => value);
}

/**
 * Type produced by applying constant `constName` to a receiver of type `receiverType`
 * (when given): the signature's conclusion, with the parameters of the receiver's binder
 * substituted from the receiver's type. `Fact.out` on `Fact (0 < T)` → `(0 < T)`.
 */
async function resultType(constName, receiverType) {
  const bc = self.VersoBinderContext;
  const hit = await loogleExact(constName);
  if (!bc || !hit || !hit.type) return null;
  let conclusion = bc.conclusionOf(hit.type);
  if (!conclusion) return null;
  if (receiverType && bc.receiverResultType) {
    // Match the receiver against its parameter as terms (handles `a ↔ b`, `a ≤ b`, …).
    const viaTerms = bc.receiverResultType(hit.type, receiverType);
    if (viaTerms) return { type: viaTerms, sig: hit.type };
  }
  const binders = signatureBinders(hit.type);
  if (receiverType) {
    const recvHead = bc.typeHead(receiverType, null);
    const strip = (x) => {
      x = x.trim();
      while (x.startsWith('(') && x.endsWith(')')) x = x.slice(1, -1).trim();
      return x;
    };
    const recvArgs = bc.splitApp(strip(receiverType)).slice(1);
    const binder = binders.find(b => bc.typeHead(b.type, null) === recvHead);
    if (binder) {
      const params = bc.splitApp(strip(binder.type)).slice(1);
      // Simultaneous substitution via placeholders (parameters may name each other's arguments).
      const subst = [];
      params.forEach((p, k) => {
        if (recvArgs[k] === undefined || !/^[\w'Ͱ-Ͽ₀-₉]+$/.test(p)) return;
        const arg = recvArgs[k];
        subst.push([p, /\s/.test(arg) && !/^\(.*\)$/.test(arg) ? `(${arg})` : arg]);
      });
      subst.forEach(([p], k) => { conclusion = replaceWord(conclusion, p, `\u0000${k}\u0000`); });
      subst.forEach(([, v], k) => { conclusion = conclusion.split(`\u0000${k}\u0000`).join(v); });
    }
  }
  // Dot notation in the conclusion (`l.SortedLE`) is typed via the signature's own binders.
  return { type: conclusion, sig: hit.type };
}

function namespaceOfType(type, sig) {
  const bc = self.VersoBinderContext;
  if (!bc || !type) return null;
  const resolveVar = (v) => {
    const vt = sig ? bc.findBinderType(v, sig) : null;
    return vt ? bc.typeHead(vt, null) : null;
  };
  return bc.typeHead(type, resolveVar);
}

/** Namespace of the type a constant produces (no receiver to substitute from). */
async function resultNamespace(constName) {
  const r = await resultType(constName, null);
  return r ? namespaceOfType(r.type, r.sig) : null;
}

/**
 * Full name of a possibly-unqualified constant at `fileRef` (via the file's
 * namespaces/opens), or the name itself.
 */
async function qualifyConstant(name, fileRef) {
  if (name.includes('.') || !fileRef) return name;
  const direct = await loogleExact(name);
  if (direct && direct.type) return name;
  const scoped = await lookupInFileScope(name, fileRef, '');
  return scoped && !scoped.ambiguous ? scoped.name : name;
}

// Anonymous projections `.1` / `.2` of common types, by name.
const NUMERIC_FIELDS = {
  'Iff': ['mp', 'mpr'], 'And': ['left', 'right'], 'Prod': ['fst', 'snd'], 'PProd': ['fst', 'snd'],
  'Sigma': ['fst', 'snd'], 'PSigma': ['fst', 'snd'], 'Subtype': ['val', 'property']
};

/** Name of field number `n` of structure `ns` (from the table, or `ns.mk`'s explicit binders). */
async function numericFieldName(ns, n) {
  if (NUMERIC_FIELDS[ns]) return NUMERIC_FIELDS[ns][n - 1] || null;
  const hit = await loogleExact(`${ns}.mk`);
  if (!hit || !hit.type) return null;
  const explicit = signatureBinders(hit.type).filter(b => b.names.length && /^\(/.test(hit.type.slice(hit.type.indexOf(b.names[0]) - 1)));
  const fields = explicit.flatMap(b => b.names);
  return fields[n - 1] || null;
}

/** `const.path₁.….field`, typing each step from Loogle signatures. */
async function resolveReceiverChain(receiver, field, fileRef) {
  if (!receiver || !receiver.const || !field) return null;
  // Track the receiver's full type, so later steps can substitute from it.
  let current = null; // { type, sig }
  if (receiver.maybeVariable) {
    // A file-level `variable` first (`hT.out` with `variable [hT : Fact (0 < T)]`).
    const v = fileRef ? await lookupFileVariable(receiver.const, fileRef) : null;
    const bc = self.VersoBinderContext;
    current = v
      ? { type: receiver.applied && bc ? bc.conclusionOf(v.rawType) : v.rawType, sig: null }
      : await resultType(await qualifyConstant(receiver.const, fileRef), null);
  } else {
    current = await resultType(await qualifyConstant(receiver.const, fileRef), null);
  }
  const named = async (ns, f) => (/^\d+$/.test(f) ? await numericFieldName(ns, parseInt(f, 10)) : f);
  for (const step of receiver.path || []) {
    const ns = current && namespaceOfType(current.type, current.sig);
    const name = ns && await named(ns, step);
    if (!name) return null;
    current = await resultType(`${ns}.${name}`, current.type);
  }
  const ns = current && namespaceOfType(current.type, current.sig);
  const name = ns && await named(ns, field);
  if (!name) return null;
  const hit = await loogleExact(`${ns}.${name}`);
  return hit && hit.type ? hitToResult(hit) : null;
}

/** `Foo` in `Foo.bar` when `Foo` is only a namespace: a short tooltip listing a few members. */
async function lookupNamespace(token, fullChain) {
  if (!/^[A-Z][\w'.]*$/.test(token)) return null;
  const hits = await queryLoogleRaw(`"${token}."`);
  const members = (hits || []).filter(h => h.name.startsWith(token + '.'));
  // The rest of the hovered name (`Order.lt_one_iff`) proves the namespace exists.
  let nsName = token;
  if (fullChain && fullChain.startsWith(token + '.') && !members.some(h => h.name === fullChain)) {
    const named = await loogleExact(fullChain);
    if (named && named.type) {
      members.unshift(named);
    } else {
      // Opened namespace: `AdjoinSimple.gen` is `IntermediateField.AdjoinSimple.gen`.
      const sub = await queryLoogleRaw(`"${fullChain}"`);
      const full = (sub || []).find(h => h.name.endsWith('.' + fullChain));
      if (full) {
        nsName = full.name.slice(0, full.name.length - fullChain.length + token.length);
        members.unshift(full);
      }
    }
  }
  if (members.length === 0) return null;
  const sample = members.slice(0, 6).map(h => `- \`${h.name}\``).join('\n');
  return {
    name: nsName, kind: 'namespace', source: 'loogle',
    typeSignature: `namespace ${nsName}`,
    docstring: `A namespace, not a declaration. Some of its members:\n\n${sample}`,
    sourceUrl: `https://leanprover-community.github.io/mathlib4_docs/find/?pattern=${encodeURIComponent(token)}#doc`
  };
}

/**
 * Conclusion of constant application `term` (`le_or_gt b 1`), with its explicit and named
 * arguments substituted: `b ≤ 1 ∨ 1 < b`.
 */
async function applicationType(term, fileRef) {
  const bc = self.VersoBinderContext;
  const head = bc && bc.applicationHead(term);
  if (!head) return null;
  const hit = await loogleExact(await qualifyConstant(head, fileRef));
  if (!hit || !hit.type) return null;
  let conclusion = bc.conclusionOf(hit.type);
  if (!conclusion) return null;
  const explicitNames = signatureBinders(hit.type).filter(b => b.explicit).flatMap(b => b.names);
  const named = {};
  const positional = [];
  for (const a of bc.splitApp(term).slice(1)) {
    const nm = a.match(/^\(\s*([\w'\u0370-\u03FF\u2080-\u209C]+)\s*:=\s*([\s\S]+)\)$/);
    if (nm) named[nm[1]] = nm[2].trim();
    else positional.push(a);
  }
  const wrap = (a) => (/\s/.test(a) && !/^[(⟨]/.test(a) ? `(${a})` : a);
  // Simultaneous substitution (`a ↦ b, b ↦ 1` must not turn `a` into `1`): placeholders first.
  const subst = [];
  explicitNames.forEach((n, k) => {
    if (positional[k] !== undefined && positional[k] !== '_') subst.push([n, wrap(positional[k])]);
  });
  for (const [n, v] of Object.entries(named)) subst.push([n, wrap(v)]);
  subst.forEach(([n], k) => { conclusion = replaceWord(conclusion, n, `\u0000${k}\u0000`); });
  subst.forEach(([, v], k) => { conclusion = conclusion.split(`\u0000${k}\u0000`).join(v); });
  // More arguments than explicit binders: the conclusion is a function; apply it.
  for (let extra = positional.length - explicitNames.length; extra > 0; extra--) {
    const cut = conclusion.indexOf(' → ');
    if (cut === -1) break;
    conclusion = conclusion.slice(cut + 3);
  }
  return { type: conclusion, name: hit.name };
}

/** Types for `obtain PAT := TERM` / `rcases TERM with PAT` when TERM is a constant application. */
async function inferPattern(request) {
  const bc = self.VersoBinderContext;
  if (!bc || !request || !request.term || !request.pattern) return null;
  const app = await applicationType(request.term, request.fileRef);
  if (!app) return null;
  const out = new Map();
  bc.destructure(bc.parsePattern(request.pattern), app.type, out);
  const types = (out.get(request.name) || []).filter(t => t.type);
  if (!types.length) return null;
  const f = bc.formatInferred(request.name, { types, caseIdx: request.caseIdx || 0 });
  return { typeSignature: f.typeSignature, note: f.note, from: app.name, conclusion: app.type };
}

/** `fn (arg := …)`: the type of fn's parameter `arg`, from its signature. */
async function lookupNamedArg(namedArg, fileRef) {
  const bc = self.VersoBinderContext;
  if (!bc || !namedArg || !namedArg.fn) return null;
  const hit = await loogleExact(await qualifyConstant(namedArg.fn, fileRef));
  const info = hit && hit.type ? bc.namedArgInfo(namedArg.arg, hit.name, hit.type) : null;
  return info || {
    name: namedArg.arg, kind: 'variable', source: 'local_var',
    typeSignature: `(${namedArg.arg} := …)`,
    docstring: `Named argument \`${namedArg.arg}\` of \`${namedArg.fn}\` (its type isn't in the visible signature, e.g. it comes from a \`variable\`).`
  };
}

async function handleLookupToken(token, subToken, fileRef, contextText, tacticPosition, receiver, namedArg, structField, fullChain) {
  queryStats.totalQueries++;

  // `field := …` in a structure instance: `Struct.field`, else say what it is.
  if (structField) {
    const hit = await loogleExact(token);
    if (hit && hit.type) return hitToResult(hit);
    return {
      name: structField.field, kind: 'variable', source: 'local_var',
      typeSignature: `${structField.field} := …`,
      docstring: `Field \`${structField.field}\` of the \`${structField.ns}\` being built here (possibly inherited from a parent structure).`
    };
  }

  if (namedArg) {
    const arg = await lookupNamedArg(namedArg, fileRef);
    if (arg) return arg;
  }

  // `adjoin.finiteDimensional` with `open IntermediateField` is the namespaced lemma
  // `IntermediateField.adjoin.finiteDimensional`, not dot notation: check that first.
  if (receiver && receiver.maybeVariable && !receiver.applied && fileRef) {
    const dotted = [receiver.const, ...(receiver.path || []), token].join('.');
    const named = await lookupInFileScope(dotted, fileRef, contextText, true);
    if (named && !named.ambiguous && named.typeSignature && !/^def /.test(named.typeSignature)) return named;
  }

  // `(f a).field` / `h.f₁.f₂.field`: Lean resolves `field` in the receiver's type.
  if (receiver) {
    const resolved = await resolveReceiverChain(receiver, token, fileRef);
    if (resolved) return resolved;
  }

  // In tactic position (`by fun_prop`, `· positivity`, `<;> simp`), a bare word is a tactic.
  if (tacticPosition && token && !token.includes('.')) {
    const tactic = await lookupTactic(token);
    if (tactic) return tactic;
  }

  // Bare identifiers depend on the file's `variable`s, `namespace`s and `open`s,
  // so they bypass the token cache.
  if (fileRef && token && !token.includes('.')) {
    const variable = await lookupFileVariable(token, fileRef);
    if (variable) return variable;
    // One-letter lowercase names are locals; uppercase ones can be constants (`X`, `C`, `I`).
    if (token.length <= 1 && !/^[A-Z]$/.test(token)) return null;
    const settings = await getSettings();
    if (settings.enableLoogle) {
      const scoped = await lookupInFileScope(token, fileRef, contextText);
      if (scoped) {
        queryStats.loogleHits++;
        return scoped;
      }
    }
  }

  // 1. Check in-memory cache
  if (memoryCache.has(token)) {
    queryStats.cacheHits++;
    return memoryCache.get(token);
  }

  // 2. Check storage cache
  const cacheKey = `cache_${CACHE_VERSION}_${token}`;
  const cached = await new Promise((res) => {
    chrome.storage.local.get([cacheKey], (result) => res(result[cacheKey]));
  });
  if (cached && Date.now() - cached.timestamp < 1000 * 60 * 60 * 24 * 7) {
    queryStats.cacheHits++;
    memoryCache.set(token, cached.data);
    return cached.data;
  }

  const settings = await getSettings();

  // 3. Try the local companion server if enabled
  if (settings.enableLocalVerso && settings.localVersoUrl) {
    const localResult = await queryLocalVerso(token, settings.localVersoUrl);
    if (localResult) {
      queryStats.localHits++;
      memoryCache.set(token, localResult);
      return localResult;
    }
  }

  // 4. Try Loogle API (with smart namespace and substring resolution)
  if (settings.enableLoogle) {
    let loogleResult = await queryLoogle(token, subToken);
    if (!loogleResult || loogleResult.ambiguous) {
      // Tactics aren't declarations, so Loogle can't find them.
      loogleResult = (await lookupTactic(token)) || loogleResult;
    }
    if ((!loogleResult || loogleResult.ambiguous) && token.includes('.') && fileRef) {
      // `Tendsto.sub` from a type head written unqualified (`open Filter`): qualify it in scope.
      const [first, ...rest] = token.split('.');
      const qualified = await qualifyConstant(first, fileRef);
      if (qualified !== first) {
        const hit = await loogleExact(`${qualified}.${rest.join('.')}`);
        if (hit && hit.type) loogleResult = hitToResult(hit);
      }
    }
    if ((!loogleResult || loogleResult.ambiguous) && token.includes('.')) {
      // `MultilinearMap.ext_iff.mp`, `Finset.univ.erase`: a constant followed by fields.
      const segs = token.split('.');
      for (let k = segs.length - 1; k >= 1 && (!loogleResult || loogleResult.ambiguous); k--) {
        const head = segs.slice(0, k).join('.');
        const exists = await loogleExact(head);
        if (!exists || !exists.type) continue;
        const viaFields = await resolveReceiverChain({ const: head, path: segs.slice(k, -1) }, segs[segs.length - 1], fileRef);
        if (viaFields) loogleResult = viaFields;
      }
    }
    // A namespace segment (`ENNReal.Tendsto` in `ENNReal.Tendsto.const_mul`) rather than a lemma.
    if ((!loogleResult || (loogleResult.ambiguous && fullChain && fullChain.startsWith(token + '.')))) {
      loogleResult = (await lookupNamespace(token, fullChain)) || loogleResult;
    }
    if (loogleResult) {
      queryStats.loogleHits++;
      // Ambiguous results may come from a transient failure of the more specific
      // queries, so keep them out of the persistent cache.
      if (!loogleResult.ambiguous) {
        memoryCache.set(token, loogleResult);
        chrome.storage.local.set({
          [cacheKey]: { timestamp: Date.now(), data: loogleResult }
        });
      }
      return loogleResult;
    }
  }

  return null;
}

/**
 * Message Dispatcher
 */
/**
 * A lookup with an alternative reading (`alt`: e.g. the codomain of a coerced bundled map):
 * use the alternative when the primary one finds nothing definite.
 */
async function handleLookupWithAlt(request) {
  const run = (token, receiver) => handleLookupToken(token, request.subToken, request.fileRef, request.contextText,
    request.tacticPosition, receiver, request.namedArg, request.structField, request.fullChain);
  const primary = await run(request.token, request.receiver);
  const alt = request.alt;
  if (alt && (!primary || primary.ambiguous || primary.kind === 'namespace')) {
    const second = alt.token ? await run(alt.token, null) : await run(alt.field, alt.chain);
    if (second && !second.ambiguous) return second;
  }
  return primary;
}

chrome.runtime.onMessage.addListener((request, sender, sendResponse) => {
  const { action } = request;

  if (action === "LOOKUP_TOKEN") {
    handleLookupWithAlt(request).then((result) => {
      sendResponse({ success: Boolean(result), data: result });
    });
    return true; // Keep message channel open for async response
  }

  if (action === "PROJECT_DECLARATIONS") {
    projectDeclarations(request).then((declarations) => sendResponse({ declarations }), () => sendResponse({ declarations: [] }));
    return true;
  }

  if (action === "CONSTANT_SIGNATURE") {
    // Statement of a rewrite rule's constant, for replaying `rw … at h` in the page.
    (async () => {
      const hit = await loogleExact(await qualifyConstant(request.name, request.fileRef));
      return hit && hit.type ? { name: hit.name, type: hit.type } : null;
    })().then(sendResponse, () => sendResponse(null));
    return true;
  }

  if (action === "INFER_PATTERN") {
    inferPattern(request).then((r) => sendResponse(r));
    return true;
  }

  if (action === "STRUCTURE_FIELD") {
    structureField(request.type, request.index, request.rest).then((f) => {
      sendResponse(f ? { field: { name: f.name, type: f.type }, structure: f.structure } : null);
    });
    return true;
  }

  if (action === "GET_SETTINGS") {
    getSettings().then((settings) => {
      sendResponse({ success: true, settings, stats: queryStats });
    });
    return true;
  }

  if (action === "SET_SETTINGS") {
    chrome.storage.local.set({ [SETTINGS_KEY]: request.settings }, () => {
      sendResponse({ success: true });
    });
    return true;
  }

  if (action === "CLEAR_CACHE") {
    memoryCache.clear();
    rawQueryCache.clear();
    fileTextCache.clear();
    tacticDocsPromise = null;
    // Remove cached lookups only; keep the user's settings.
    chrome.storage.local.get(null, (all) => {
      const keys = Object.keys(all || {}).filter(k => k.startsWith('cache_') || k === TACTIC_CACHE_KEY);
      chrome.storage.local.remove(keys, () => sendResponse({ success: true }));
    });
    return true;
  }

  if (action === "TEST_LOCAL_SERVER") {
    queryLocalVerso("Nat", request.url || "http://127.0.0.1:8000").then((res) => {
      sendResponse({ success: Boolean(res), details: res });
    });
    return true;
  }
});
