/**
 * A Lean file's outline, read from its source: its declarations, and the commands that change
 * what a declaration sees (`namespace`, `section`, `end`, `open`, `variable`, `include`,
 * `omit`, `universe`, `set_option`), each with its line.
 *
 * Also what is in force at a line (what Mathlib's `#where` prints there), and where a
 * declaration might belong in its file: next to the declarations most like it.
 *
 * Read from the text alone, so it follows Lean's layout conventions rather than its parser:
 * commands start at the beginning of a line, and what is indented belongs to the command above.
 */
(function (scope) {
  const DECL_KINDS = ['theorem', 'lemma', 'def', 'abbrev', 'instance', 'opaque', 'example', 'structure', 'class',
    'inductive', 'coinductive', 'axiom', 'irreducible_def', 'alias', 'noncomputable def'];
  const MODIFIERS = '(?:private|protected|public|noncomputable|scoped|partial|nonrec|unsafe|meta|local)';
  const DECL_RE = new RegExp(
    `^((?:@\\[[^\\]]*\\]\\s*)*)((?:${MODIFIERS}\\s+)*)(class\\s+inductive|theorem|lemma|def|abbrev|instance|opaque|example|structure|class|inductive|coinductive|axiom|irreducible_def|alias)\\b\\s*(.*)$`);
  // A command with ` in` after it applies to the next command only (`open Real in`).
  const PREFIX_IN = /^((?:open|omit|include|set_option|variable)\b.*?)\s+in\b\s*(.*)$/;
  const SCOPE_CMDS = /^(namespace|section|end|open|variable|include|omit|universe|set_option|export)\b/;
  const OTHER_CMDS = /^(?:(?:local|scoped)\s+)?(?:notation|infix[lr]?|prefix|postfix|macro|macro_rules|syntax|elab|elab_rules|attribute|initialize|builtin_initialize|deriving|mutual|#\w+)\b/;
  // The module header: `module`, `prelude`, `import A`, `public import A`, `public meta import A`.
  const IMPORT = /^(?:module|prelude)\b|^(?:(?:public|private)\s+)?(?:meta\s+)?import\b/;
  // Lines at the start of a line that still belong to the command above.
  const CONTINUES = /^(?:\||where\b|deriving\b|termination_by\b|decreasing_by\b|with\b|:=|\)|\]|\}|⟩|·|<;>)/;

  /** Lines without comments (block comments may span lines; nesting is counted). */
  function codeLines(text) {
    const state = { depth: 0 };
    return String(text || '').split('\n').map((line) => {
      let out = '';
      let inString = false;
      for (let i = 0; i < line.length; i++) {
        if (state.depth === 0 && line[i] === '"' && line[i - 1] !== '\\') inString = !inString;
        if (inString) { out += line[i]; continue; }
        if (line.startsWith('/-', i)) { state.depth++; i++; continue; }
        if (state.depth > 0) {
          if (line.startsWith('-/', i)) { state.depth--; i++; }
          continue;
        }
        if (line.startsWith('--', i)) break;
        out += line[i];
      }
      return out.replace(/\s+$/, '');
    });
  }

  /** The name a declaration header gives (`foo` in `foo {α} : …`), or ''. */
  function headerName(kind, rest) {
    if (kind === 'example') return '';
    if (kind === 'instance') {
      // `instance foo : C` is named; `instance : C` and `instance [h] : C` are not.
      const m = rest.match(/^(?:\(priority\s*:=\s*[^)]*\)\s*)?([^\s(:{[⦃]+)/);
      return m && !/^:/.test(m[1]) ? m[1] : '';
    }
    const m = rest.match(/^([^\s(:{[⦃]+)/);
    return m ? m[1] : '';
  }

  /**
   * The file's commands, in order. Each is
   * `{kind, line, endLine, text, depth}` and, for a declaration, `declKind`, `name` (as
   * written), `fullName` (with the namespaces around it), `attrs` and `prefixes` (the
   * `open … in`-style commands that apply to it alone). `kind` is 'decl', a scope command's
   * keyword ('namespace', 'variable', …) or 'command' for other commands (`notation`, `#check`).
   */
  function outline(text) {
    const lines = String(text || '').split('\n');
    const code = codeLines(text);
    const entries = [];
    const namespaces = [];
    const frames = [];
    let pendingAttrs = [];
    let pendingPrefixes = [];
    let pendingStart = null;
    let last = null;

    const close = (entry, upTo) => {
      if (!entry) return;
      let end = upTo;
      while (end > entry.line && !code[end - 1].trim()) end--;
      entry.endLine = Math.max(entry.line, end);
    };

    for (let i = 0; i < lines.length; i++) {
      const raw = code[i];
      if (!raw.trim()) continue;
      const lineNo = i + 1;
      if (/^\s/.test(raw) || CONTINUES.test(raw)) continue; // part of the command above
      close(last, i);
      last = null;
      let t = raw.trim();

      // `@[simp]` alone on its line: the attributes of the declaration below.
      if (/^@\[[^\]]*\]$/.test(t)) {
        pendingAttrs.push(t);
        if (pendingStart === null) pendingStart = lineNo;
        continue;
      }
      let m;
      while ((m = t.match(PREFIX_IN))) {
        pendingPrefixes.push(m[1].trim());
        if (pendingStart === null) pendingStart = lineNo;
        t = m[2].trim();
      }
      if (!t) continue;

      const depth = frames.length;
      const entry = { line: lineNo, endLine: lineNo, text: raw.trim(), depth };
      if ((m = t.match(DECL_RE))) {
        const attrs = pendingAttrs.concat(m[1].trim() ? [m[1].trim()] : []);
        const declKind = m[3].replace(/\s+/, ' ');
        const name = headerName(declKind, m[4]);
        let fullName = name;
        if (name.startsWith('_root_.')) fullName = name.slice(7);
        else if (name && namespaces.length) fullName = `${namespaces.join('.')}.${name}`;
        Object.assign(entry, {
          kind: 'decl', declKind, name, fullName, attrs, prefixes: pendingPrefixes,
          modifiers: m[2].trim(), startLine: pendingStart || lineNo
        });
      } else if ((m = t.match(SCOPE_CMDS))) {
        entry.kind = m[1];
        if (m[1] === 'namespace') {
          entry.name = (t.match(/^namespace\s+(\S+)/) || [])[1] || '';
          frames.push({ kind: 'namespace', name: entry.name, line: lineNo });
          namespaces.push(entry.name);
        } else if (m[1] === 'section') {
          entry.name = (t.match(/^section\s+(\S+)/) || [])[1] || '';
          frames.push({ kind: 'section', name: entry.name, line: lineNo });
        } else if (m[1] === 'end') {
          entry.name = (t.match(/^end\s+(\S+)/) || [])[1] || '';
          const frame = frames.pop();
          if (frame && frame.kind === 'namespace') namespaces.pop();
          entry.depth = frames.length;
        }
      } else if (/^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|public\s+|private\s+)*section\b/.test(t)) {
        entry.kind = 'section';
        entry.name = (t.match(/section\s+(\S+)/) || [])[1] || '';
        frames.push({ kind: 'section', name: entry.name, line: lineNo });
      } else if (OTHER_CMDS.test(t) || IMPORT.test(t)) {
        entry.kind = IMPORT.test(t) ? 'import' : 'command';
      } else {
        continue; // not a command (a stray line)
      }
      if (entry.kind !== 'decl' && entry.kind !== 'command') { pendingAttrs = []; }
      if (entry.kind === 'decl' || entry.kind === 'command') {
        pendingAttrs = [];
      }
      if (entry.kind === 'decl' || entry.kind === 'command' || entry.kind === 'import') {
        entry.prefixes = entry.prefixes || pendingPrefixes;
        pendingPrefixes = [];
      }
      pendingStart = null;
      entries.push(entry);
      last = entry;
    }
    close(last, lines.length);
    // A command's full text (its continuation lines), for those whose text matters.
    for (const e of entries) {
      if (e.endLine > e.line && /^(variable|include|omit|open|universe|set_option)$/.test(e.kind)) {
        e.text = code.slice(e.line - 1, e.endLine).filter((l) => l.trim()).join('\n').trim();
      }
    }
    return entries;
  }

  /**
   * What is in force at 1-based `line`, from the commands above it: `{frames, namespace,
   * commands, decl}`. `frames` are the open `namespace`s and `section`s (outermost first);
   * `commands` the `open`, `variable`, `include`, `omit`, `universe` and `set_option` commands
   * still in scope, in order, with the frame each is in; `decl` the declaration at the line
   * (with the `… in` commands that apply to it alone), or null.
   */
  function contextAt(text, line, entries = outline(text)) {
    const frames = [];
    let commands = [];
    let decl = null;
    for (const e of entries) {
      if (e.line > line) break;
      if (e.kind === 'decl' && e.line <= line && line <= e.endLine) decl = e;
      if (e.line === line && e.kind !== 'decl') continue; // the command being hovered itself
      if (e.kind === 'namespace' || e.kind === 'section') {
        frames.push({ kind: e.kind, name: e.name, line: e.line, text: e.text });
      } else if (e.kind === 'end') {
        frames.pop();
        // What the closed frame brought into scope goes with it.
        commands = commands.filter((c) => c.depth <= frames.length);
      } else if (/^(open|variable|include|omit|universe|set_option|export)$/.test(e.kind)) {
        commands.push({ kind: e.kind, text: e.text, line: e.line, depth: frames.length });
      }
    }
    if (decl && decl.startLine > line) decl = null;
    const namespace = frames.filter((f) => f.kind === 'namespace').map((f) => f.name).join('.');
    return { frames, namespace, commands, decl };
  }

  /**
   * The context at a line as Lean code, like `#where`'s output: the namespaces and sections,
   * then the commands in force, each marked with its line.
   */
  function whereText(ctx) {
    const out = [];
    const mark = (s, line) => `${s}  -- line ${line}`;
    let depth = 0;
    const indentFor = () => '  '.repeat(depth);
    let ci = 0;
    const commandsAt = (d) => {
      while (ci < ctx.commands.length && ctx.commands[ci].depth <= d) {
        const c = ctx.commands[ci++];
        const lines = c.text.split('\n');
        out.push(indentFor() + mark(lines[0], c.line));
        lines.slice(1).forEach((l) => out.push(indentFor() + l));
      }
    };
    commandsAt(0);
    ctx.frames.forEach((f, i) => {
      // As written (`noncomputable section`, `@[expose] public section`).
      out.push(indentFor() + mark(f.text || `${f.kind}${f.name ? ` ${f.name}` : ''}`, f.line));
      depth = i + 1;
      commandsAt(i + 1);
    });
    if (ctx.decl && ctx.decl.prefixes && ctx.decl.prefixes.length) {
      ctx.decl.prefixes.forEach((p) => out.push(indentFor() + mark(`${p} in`, ctx.decl.startLine)));
    }
    return out.join('\n');
  }

  // --- Where a declaration belongs: the declarations most like it in the same file. ---

  // Words that name two sides of one thing: `isOpen` and `isClosed` are about the same.
  const DUALS = [['open', 'closed'], ['left', 'right'], ['min', 'max'], ['inf', 'sup'], ['top', 'bot'],
    ['succ', 'pred'], ['pos', 'neg'], ['lt', 'gt'], ['le', 'ge'], ['upper', 'lower'], ['injective', 'surjective'],
    ['mono', 'anti'], ['monotone', 'antitone'], ['image', 'preimage'], ['fst', 'snd'], ['zero', 'one'],
    ['add', 'mul'], ['sub', 'div'], ['neg', 'inv'], ['sum', 'prod'], ['nsmul', 'pow'], ['zsmul', 'zpow'],
    ['head', 'tail'], ['inl', 'inr'], ['mem', 'notMem'], ['nonneg', 'nonpos'], ['even', 'odd'], ['union', 'inter'],
    ['ne', 'eq'], ['iff', 'imp'], ['comp', 'id'], ['map', 'comap'], ['ker', 'range'], ['continuous', 'continuousOn'],
    ['finite', 'infinite'], ['countable', 'uncountable'], ['ext', 'ext_iff']];
  const DUAL_OF = new Map();
  for (const [a, b] of DUALS) { DUAL_OF.set(a, b); DUAL_OF.set(b, a); }

  /** The words of a declaration name: `Set.isOpen_iff'` → `set is open iff`. */
  function nameWords(name) {
    return String(name || '')
      .replace(/[«»]/g, '')
      .split(/[._]+/)
      .flatMap((part) => part.replace(/([a-z0-9])([A-Z])/g, '$1 $2').replace(/([A-Z]+)([A-Z][a-z])/g, '$1 $2').split(/\s+/))
      .map((w) => w.replace(/['!?₀-₉]+$/u, '').toLowerCase())
      .filter(Boolean);
  }

  /** The name without what tells variants apart: `foo'`, `foo₂`, `foo_of_le` stays itself. */
  const baseName = (name) => String(name || '').split('.').pop().replace(/['₀-₉]+$/u, '');

  function trigrams(s) {
    const out = new Map();
    const t = ` ${s} `;
    for (let i = 0; i + 3 <= t.length; i++) out.set(t.slice(i, i + 3), (out.get(t.slice(i, i + 3)) || 0) + 1);
    return out;
  }
  function cosine(a, b) {
    let dot = 0;
    let na = 0;
    let nb = 0;
    for (const [k, v] of a) { na += v * v; if (b.has(k)) dot += v * b.get(k); }
    for (const v of b.values()) nb += v * v;
    return na && nb ? dot / Math.sqrt(na * nb) : 0;
  }

  /** How alike two word lists are (a dual word counts nearly as the same word). */
  function wordSimilarity(a, b) {
    if (!a.length || !b.length) return 0;
    const rest = b.slice();
    let shared = 0;
    for (const w of a) {
      let k = rest.indexOf(w);
      if (k !== -1) { shared += 1; rest.splice(k, 1); continue; }
      k = rest.indexOf(DUAL_OF.get(w));
      if (k !== -1) { shared += 0.8; rest.splice(k, 1); }
    }
    return shared / (a.length + b.length - shared);
  }

  // Names in a statement that say what it is about (not its variables or syntax).
  const STOP = new Set(['Type', 'Prop', 'Sort', 'fun', 'by', 'have', 'show', 'from', 'at', 'with', 'if', 'then', 'else',
    'let', 'in', 'do', 'match', 'Nat', 'Int', 'ℕ', 'ℤ', 'ℝ', 'ℚ', 'ℂ', 'True', 'False']);
  function statementNames(statement) {
    const out = new Set();
    for (const m of String(statement || '').matchAll(/[A-Za-z_][\w'.]*[\w']|[A-Za-z]/g)) {
      const w = m[0];
      if (w.length < 3 || STOP.has(w)) continue;
      if (/^[A-Z]/.test(w) || w.includes('.')) out.add(w);
    }
    return out;
  }
  function jaccard(a, b) {
    if (!a.size || !b.size) return 0;
    let shared = 0;
    for (const x of a) if (b.has(x)) shared++;
    return shared / (a.size + b.size - shared);
  }

  /** A declaration's features for comparing it with others (cached on the entry). */
  function featuresOf(decl, lines) {
    if (decl.features) return decl.features;
    const short = decl.name.replace(/^_root_\./, '');
    const words = nameWords(short);
    const statement = lines.slice(decl.line - 1, Math.min(decl.endLine, decl.line + 8)).join('\n').split(':=')[0];
    decl.features = { words, grams: trigrams(words.join('')), base: baseName(short), names: statementNames(statement) };
    return decl.features;
  }

  /** How alike two declarations are, from 0 to 1: mostly by name, partly by what they state. */
  function similarity(a, b, lines) {
    const fa = featuresOf(a, lines);
    const fb = featuresOf(b, lines);
    if (fa.base && fa.base === fb.base) return 1; // `foo` and `foo'`
    const byName = 0.6 * wordSimilarity(fa.words, fb.words) + 0.4 * cosine(fa.grams, fb.grams);
    // (Statements that name nothing to compare say nothing either way.)
    if (!fa.names.size || !fb.names.size) return byName;
    return 0.75 * byName + 0.25 * jaccard(fa.names, fb.names);
  }

  const FAMILY = 0.72; // this alike or more: declarations that go together
  const SIMILAR = 0.5; // this alike or more: worth naming as similar

  /**
   * For each named declaration (or only those whose header line is in `lines`, when given): the
   * declarations most like it in the file, and hints where they suggest it belongs.
   * Returns `[{line, name, similar: [{name, line, score}], hints: [{kind, text, line}]}]`:
   *   - 'split': it sits between two declarations that belong together (`foo` … `foo'`);
   *   - 'far': it is much more like a declaration elsewhere in the file than like those around it.
   */
  function placementHints(text, onlyLines = null, entries = outline(text)) {
    const lines = String(text || '').split('\n');
    const decls = entries.filter((e) => e.kind === 'decl' && e.name);
    const out = [];
    decls.forEach((d, i) => {
      if (onlyLines && !onlyLines.has(d.line)) return;
      const scored = decls.map((o, k) => ({ o, k, score: k === i ? -1 : similarity(d, o, lines) }))
        .filter((x) => x.k !== i)
        .sort((x, y) => y.score - x.score);
      const similar = scored.filter((x) => x.score >= SIMILAR).slice(0, 3)
        .map((x) => ({ name: x.o.name, line: x.o.line, score: Math.round(x.score * 100) / 100 }));
      const hints = [];
      const prev = decls[i - 1];
      const next = decls[i + 1];
      const near = (o) => (o ? similarity(d, o, lines) : 0);
      const together = prev && next ? similarity(prev, next, lines) : 0;
      // Between two that go together, and not one of them itself (`foo`, new, `foo'`).
      if (prev && next && together >= FAMILY && Math.max(near(prev), near(next)) < together - 0.2) {
        hints.push({
          kind: 'split', line: prev.line,
          text: `It separates \`${prev.name}\` (line ${prev.line}) from \`${next.name}\` (line ${next.line}), which belong together.`
        });
      }
      const best = scored[0];
      const around = Math.max(near(prev), near(next));
      if (best && best.score >= SIMILAR + 0.1 && best.o !== prev && best.o !== next && best.score >= around + 0.25) {
        const ctxHere = contextAt(text, d.line, entries).namespace;
        const ctxThere = contextAt(text, best.o.line, entries).namespace;
        const where = ctxThere !== ctxHere ? ` (in ${ctxThere ? `namespace \`${ctxThere}\`` : 'no namespace'})` : '';
        hints.push({
          kind: 'far', line: best.o.line,
          text: `Most like \`${best.o.name}\` at line ${best.o.line}${where}: it may belong next to it.`
        });
      }
      out.push({ line: d.line, name: d.name, similar, hints });
    });
    return out;
  }

  /**
   * The lines of `after` that are not in `before` (1-based), from their longest common
   * subsequence of lines. A file too large to compare counts as changed where it differs.
   */
  function addedLines(before, after) {
    const a = String(before || '').split('\n');
    const b = String(after || '').split('\n');
    const added = new Set();
    if (before === null || before === undefined) { b.forEach((_, i) => added.add(i + 1)); return added; }
    let lo = 0;
    while (lo < a.length && lo < b.length && a[lo] === b[lo]) lo++;
    let ea = a.length;
    let eb = b.length;
    while (ea > lo && eb > lo && a[ea - 1] === b[eb - 1]) { ea--; eb--; }
    const n = ea - lo;
    const m = eb - lo;
    if (n * m > 6e6) { for (let j = lo; j < eb; j++) added.add(j + 1); return added; }
    const table = new Array(n + 1);
    for (let i = 0; i <= n; i++) table[i] = new Uint32Array(m + 1);
    for (let i = n - 1; i >= 0; i--) {
      for (let j = m - 1; j >= 0; j--) {
        table[i][j] = a[lo + i] === b[lo + j] ? table[i + 1][j + 1] + 1 : Math.max(table[i + 1][j], table[i][j + 1]);
      }
    }
    let i = 0;
    let j = 0;
    while (j < m) {
      if (i < n && a[lo + i] === b[lo + j]) { i++; j++; }
      else if (i < n && table[i + 1][j] >= table[i][j + 1]) i++;
      else { added.add(lo + j + 1); j++; }
    }
    return added;
  }

  scope.LeanOutline = { outline, contextAt, whereText, placementHints, addedLines, nameWords, similarity, DECL_KINDS };
})(typeof self !== 'undefined' ? self : globalThis);
