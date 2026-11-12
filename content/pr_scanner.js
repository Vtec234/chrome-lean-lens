/**
 * Lean 4 In-PR Declaration Scanner.
 * Parses Pull Request diffs and commit changes on GitHub to index newly defined
 * theorems, lemmas, definitions, and structures directly within the PR!
 * Supports classic diffs and the new React-based /changes PR interface.
 */

(function () {
  // `theorem foo …`, with attributes and modifiers; group 1 = kind, 2 = name, 3 = the rest.
  const DECL_REGEX = /^(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|public\s+|noncomputable\s+|scoped\s+|partial\s+|nonrec\s+|unsafe\s+|meta\s+)*(theorem|lemma|def|inductive|structure|class|abbrev|opaque|instance|alias)\s+([A-Za-z0-9_'.\u0370-\u03FF\u2070-\u209F]+)([\s\S]*)/;
  const SIG_END = /:=|\bwhere\b|(^|\s)by\b|^\s*\|/;

  /**
   * A declaration's signature as Lean's hover prints it (`foo (x : ℝ) : P`); aliases as written.
   * `known(name)`: signatures of the declarations before it (for `(tprod R) f` coercions).
   */
  function leanStyle(kind, name, body, known = null) {
    const bc = (typeof window !== 'undefined' ? window : self).VersoBinderContext;
    if (kind === 'alias' || !bc || !bc.leanSignature) return `${kind} ${name}${body ? ' ' + body : ''}`;
    return bc.leanSignature(name, body, known);
  }

  /**
   * Where a declaration's signature ends: the first `:=`, `where`, ` by` or leading `|` at
   * bracket depth 0 (a parameter's default value, `(hq : P := by simp)`, is inside it). -1 if none.
   */
  function signatureEnd(text, alias) {
    if (alias) return -1;
    const open = '([{⦃⟨', close = ')]}⦄⟩';
    let depth = 0;
    for (let i = 0; i < text.length; i++) {
      const ch = text[i];
      if (open.includes(ch)) depth++;
      else if (close.includes(ch)) depth = Math.max(0, depth - 1);
      else if (depth === 0) {
        if (text.startsWith(':=', i)) return i;
        const prev = i === 0 ? '\n' : text[i - 1];
        if (/\s/.test(prev) && /^(where|by)\b/.test(text.slice(i, i + 6))) return i - 1;
        if (prev === '\n' && /^\s*\|/.test(text.slice(i))) return i;
      }
    }
    return -1;
  }

  // --- Section variables: which `variable`s a declaration takes, as Lean decides ---
  //
  // A declaration gets the section variables it mentions (a `def` in its body too, a `theorem`
  // only in its statement), the variables those depend on, and every instance argument whose
  // variables are all included. `variable {K} in` / `omit [..] in` / `include x in` change this
  // for the next declaration only; without `in`, until the end of the section.

  const BR_OPEN = '([{⦃⟨', BR_CLOSE = ')]}⦄⟩';
  const IDENT_RE = /[A-Za-z_Ͱ-Ͽἀ-῿℀-⅏][\w'!?Ͱ-Ͽἀ-῿₀-ₜ℀-⅏]*/g;
  const namesOf = (s) => new Set(((s || '').replace(/--[^\n]*/g, ' ').match(IDENT_RE)) || []);
  const norm = (s) => (s || '').replace(/\s+/g, ' ').trim();

  function closeOf(t, i) {
    for (let k = i + 1, depth = 0; k < t.length; k++) {
      if (BR_OPEN.includes(t[k])) depth++;
      else if (BR_CLOSE.includes(t[k])) { if (depth === 0) return k; depth--; }
    }
    return -1;
  }

  /** Index of ` : ` at bracket depth 0 in a binder group's inside, or -1. */
  function groupColon(t) {
    for (let k = 0, depth = 0; k < t.length; k++) {
      if (BR_OPEN.includes(t[k])) depth++;
      else if (BR_CLOSE.includes(t[k])) depth--;
      else if (depth === 0 && t[k] === ':' && t[k + 1] !== '=') return k;
    }
    return -1;
  }

  /** Binder groups `(K L : Type*)`, `[NormedField K]`, `{K L}` (an update, no type), and bare names. */
  function binderGroups(text) {
    const groups = [];
    const bare = [];
    for (let i = 0; i < text.length;) {
      const ch = text[i];
      if ('({[⦃'.includes(ch)) {
        const close = closeOf(text, i);
        if (close === -1) break;
        const inner = text.slice(i + 1, close).trim();
        const c = groupColon(inner);
        if (c === -1) groups.push(ch === '[' ? { bi: ch, names: [], type: inner } : { bi: ch, names: inner.split(/\s+/).filter(Boolean), type: null });
        else groups.push({ bi: ch, names: inner.slice(0, c).trim().split(/\s+/).filter(Boolean), type: inner.slice(c + 1).trim() });
        i = close + 1;
      } else {
        const m = text.slice(i).match(/^[^\s({[⦃]+/);
        if (m) { bare.push(m[0]); i += m[0].length; } else i++;
      }
    }
    return { groups, bare };
  }

  /** The text before a top-level `in` keyword (a one-shot command) and after it, or null. */
  function splitIn(text) {
    for (let k = 0, depth = 0; k < text.length; k++) {
      const ch = text[k];
      if (BR_OPEN.includes(ch)) depth++;
      else if (BR_CLOSE.includes(ch)) depth--;
      else if (depth === 0 && /\s/.test(text[k - 1] || ' ') && /^in(?![\w'])/.test(text.slice(k))) {
        return { args: text.slice(0, k), after: text.slice(k + 2).trim() };
      }
    }
    return null;
  }

  // Classes with out-params: Lean finds an instance variable of one by instance synthesis when
  // the declaration elaborates something that needs it, and then takes it and its out-param.
  // `M ≃ₛₗ[σ] M₂` needs `RingHomInvPair σ ?σ'`; `g ∘ₛₗ f` needs `RingHomCompTriple σ₁₂ σ₂₃ ?σ₁₃`.
  // `uses(text, args)` says whether `text` needs the instance with those (given) arguments.
  const OUT_PARAM_CLASSES = {
    RingHomInvPair: (text, a) => new RegExp(`≃ₛₗ\\[\\s*${a[0].replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\s*\\]`).test(text),
    RingHomCompTriple: (text) => /∘ₛₗ|(?:^|[^\w'])(?:LinearMap\.)?comp\b(?!\w)|≪≫ₗ|LinearEquiv\.trans\b/.test(text.replace(/\.comp(?=[\w'])/g, ''))
  };

  class VariableScope {
    constructor() { this.frames = [VariableScope.frame()]; this.pending = null; this.seq = 0; }
    static frame() { return { vars: [], updates: [], omits: [], includes: [] }; }
    push() { this.frames.push(VariableScope.frame()); }
    pop() { if (this.frames.length > 1) this.frames.pop(); }

    /**
     * A `variable` / `omit` / `include` command (text after the keyword). With a top-level
     * `in`, it applies to the next declaration only; returns the text after `in` (maybe a
     * declaration on the same line). Every variable and change gets a sequence number: a
     * name means the latest variable declared before it.
     */
    command(keyword, text) {
      const split = splitIn(text);
      const target = split ? (this.pending = this.pending || VariableScope.frame()) : this.frames[this.frames.length - 1];
      const { groups, bare } = binderGroups(split ? split.args : text);
      const seq = () => ++this.seq;
      if (keyword === 'variable') {
        for (const g of groups) {
          if (g.type === null) g.names.forEach(n => target.updates.push({ name: n, bi: g.bi, seq: seq() })); // `variable {K L}`: binder kinds
          else if (g.bi === '[' && !g.names.length) target.vars.push({ bi: '[', name: null, type: g.type, seq: seq() });
          else g.names.forEach(n => target.vars.push({ bi: g.bi, name: n, type: g.type, seq: seq() }));
        }
      } else if (keyword === 'omit') {
        groups.forEach(g => (g.bi === '[' && !g.names.length ? target.omits.push({ type: norm(g.type), seq: seq() }) : g.names.forEach(n => target.omits.push({ name: n, seq: seq() }))));
        bare.forEach(n => target.omits.push({ name: n, seq: seq() }));
      } else if (keyword === 'include') {
        [...groups.flatMap(g => g.names), ...bare].forEach(n => target.includes.push({ name: n, seq: seq() }));
      }
      return split ? split.after : '';
    }

    /**
     * The variables in scope at a declaration, in order (shadowed ones too, which Lean still
     * elaborates): [{ bi, name, type, included }], where `included` marks the ones it takes.
     * `header` is its own binders and type; `body` what follows (counted for definitions,
     * not theorems).
     */
    variablesFor(kind, header, body) {
      const frames = this.pending ? [...this.frames, this.pending] : this.frames;
      const all = frames.flatMap(f => f.vars);
      if (!all.length) return [];
      const updates = frames.flatMap(f => f.updates);
      // The variable `name` means at `seq`: the latest declared before it.
      const at = (name, seq) => { for (let k = all.length - 1; k >= 0; k--) if (all[k].name === name && all[k].seq < seq) return k; return -1; };
      const omitted = new Set();
      for (const o of frames.flatMap(f => f.omits)) {
        if (o.name) { const k = at(o.name, o.seq); if (k !== -1) omitted.add(k); }
        else all.forEach((v, k) => { if (v.bi === '[' && v.seq < o.seq && norm(v.type) === o.type) omitted.add(k); });
      }
      const deps = all.map((v, k) => [...namesOf(v.type)].map(n => at(n, v.seq)).filter(j => j !== -1 && j !== k));
      const biOf = (k) => {
        let best = null;
        for (const u of updates) if (u.name === all[k].name && u.seq > all[k].seq && at(u.name, u.seq) === k && (!best || u.seq > best.seq)) best = u;
        return best ? best.bi : all[k].bi;
      };
      // Names the declaration uses free, minus its own binders (which shadow variables).
      const bc = (typeof window !== 'undefined' ? window : self).VersoBinderContext;
      const own = new Set(binderGroups(header.slice(0, Math.max(0, groupColon(header)))).groups.flatMap(g => g.names));
      const counted = /^(theorem|lemma)$/.test(kind) ? header : `${header}\n${body || ''}`;
      const used = bc && bc.freeNamesInText ? bc.freeNamesInText(counted) : namesOf(counted);
      own.forEach(n => used.delete(n));
      const chosen = new Set();
      const add = (k) => { if (k === -1 || chosen.has(k) || omitted.has(k)) return; chosen.add(k); deps[k].forEach(add); };
      used.forEach(n => add(at(n, Infinity)));
      frames.flatMap(f => f.includes).forEach(inc => add(at(inc.name, inc.seq)));
      // Instances: those whose variables are all included, and out-param ones a term needs.
      const needs = (v, k) => {
        const m = (v.type || '').trim().match(/^([\w.']+)\s+([\s\S]+)$/);
        const uses = m && OUT_PARAM_CLASSES[m[1].split('.').pop()];
        if (!uses) return false;
        const args = m[2].trim().split(/\s+/);
        if (m[1].endsWith('RingHomInvPair') ? !chosen.has(at(args[0], v.seq)) : !args.slice(0, 2).every(a => chosen.has(at(a, v.seq)))) return false;
        return uses(counted, args) || [...chosen].some(j => all[j].type && uses(all[j].type, args));
      };
      for (let changed = true; changed;) {
        changed = false;
        all.forEach((v, k) => {
          if (chosen.has(k) || omitted.has(k) || v.bi !== '[') return;
          if (deps[k].every(j => chosen.has(j)) || needs(v, k)) { add(k); changed = true; }
        });
      }
      // A variable shadowed by a later one prints as `s✝`, in its binder and where it is used.
      const shadowed = (k) => all.some((w, j) => j > k && w.name && w.name === all[k].name);
      const dagger = (v, k) => {
        let type = v.type;
        deps[k].filter(shadowed).forEach(j => { type = type.replace(new RegExp(`(?<![\\w'.])${all[j].name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}(?![\\w'])`, 'g'), `${all[j].name}✝`); });
        return type;
      };
      return all.map((v, k) => ({ bi: biOf(k), name: v.name && shadowed(k) ? `${v.name}✝` : v.name, type: dagger(v, k), included: chosen.has(k) }));
    }

    /** After a declaration: one-shot changes are used up. */
    declared() { this.pending = null; }

    /** A copy of the current scope (frames are shared: take it after the last change). */
    snapshot() {
      const v = new VariableScope();
      v.frames = this.frames.slice();
      v.pending = this.pending;
      v.seq = this.seq;
      return v;
    }
  }

  /** Name `Type*` / `Sort*` as Lean does: `Type u_1`, `Type u_2`, … in order, skipping names in use. */
  function universeNamer(texts) {
    let k = 0;
    const used = new Set([].concat(...texts.map(t => (t || '').match(/\bu_\d+\b/g) || [])));
    const fresh = () => { do k++; while (used.has(`u_${k}`)); return `u_${k}`; };
    return (t) => (t || '').replace(/\b(Type|Sort)\*/g, (m, s) => `${s} ${fresh()}`);
  }

  const CLOSE_OF = { '(': ')', '{': '}', '[': ']', '⦃': '⦄' };

  /**
   * The signature Lean gives a declaration: the variables it takes, then its own binders and
   * type. `Type*` / `Sort*` are named `Type u_1`, `Type u_2`, … in order over all the variables
   * in scope (Lean elaborates them all, then drops the unused ones), then its own binders.
   */
  function withVariables(vars, header) {
    const named = universeNamer([header, ...vars.map(v => v.type)]);
    const binders = vars.map(v => ({ bi: v.bi, name: v.name, type: named(v.type), included: v.included })).filter(v => v.included);
    const own = named(header);
    // Consecutive variables with the same binder kind and type print as one group (`{a b : ℝ}`).
    const parts = [];
    for (const b of binders) {
      const last = parts[parts.length - 1];
      if (b.bi === '[') parts.push(b.name ? `[${b.name} : ${b.type}]` : `[${b.type}]`);
      else if (last && last.bi === b.bi && last.type === b.type) last.names.push(b.name);
      else parts.push({ bi: b.bi, names: [b.name], type: b.type });
    }
    const text = parts.map(p => (typeof p === 'string' ? p : `${p.bi}${p.names.join(' ')} : ${p.type}${CLOSE_OF[p.bi]}`)).join(' ');
    return text ? `${text} ${own}`.trim() : own;
  }

  // A command that isn't a declaration we index but ends a `… in` chain (`example`, `instance : …`).
  const OTHER_COMMAND = /^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|public|noncomputable|scoped|local|partial|nonrec|unsafe|meta)\s+)*(?:example|instance|theorem|lemma|def|abbrev|structure|class|inductive|opaque|axiom|alias|attribute|macro|syntax|notation|elab|infix|infixl|infixr|prefix|postfix)\b/;
  const SCOPE_OPEN = /^(?:namespace\s+\S+|(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|public|private)\s+)*section\b)/;

  /**
   * Feed one line to the variable scope. Returns { skip: lines consumed beyond this one,
   * rest: text left on the line (a declaration after `variable … in`) } for a scope command,
   * or null for anything else.
   */
  function trackScope(vscope, t, lineAt, i) {
    if (SCOPE_OPEN.test(t)) { vscope.declared(); vscope.push(); return { skip: 0, rest: '' }; }
    if (/^end\b/.test(t)) { vscope.declared(); vscope.pop(); return { skip: 0, rest: '' }; }
    const cmd = t.match(/^(variable|omit|include)\b([\s\S]*)$/);
    if (!cmd) return null;
    // The command continues on indented lines.
    let text = cmd[2];
    let j = i + 1;
    for (let line = lineAt(j); line !== null && /^\s+\S/.test(line) && !DECL_REGEX.test(line.trim()); line = lineAt(++j)) text += '\n' + line;
    return { skip: j - i - 1, rest: vscope.command(cmd[1], text) };
  }

  /** A definition's body: the rest of its signature text, then the indented lines after it. */
  function bodyAfter(rest, sigEnd, lineAt, from) {
    let body = sigEnd !== -1 ? rest.slice(sigEnd) : '';
    for (let j = from, n = 0; n < 400; j++, n++) {
      const line = lineAt(j);
      if (line === null || (line.trim() && !/^\s/.test(line))) break;
      body += '\n' + line;
    }
    return body;
  }

  class LeanPRScanner {
    constructor() {
      this.declarations = new Map();
      // Keys that only hold a dotted declaration's last component (`tprod` for `lift.tprod`):
      // a declaration of that exact name replaces it.
      this.viaShort = new Set();
      this.isScanning = false;
      this.lastScanTime = 0;
      this.scannedFileCount = 0;
    }

    /**
     * Clear all cached PR declarations.
     */
    reset() {
      this.declarations.clear();
      this.viaShort.clear();
      this.scannedFileCount = 0;
    }

    /**
     * Find declaration by exact token or suffix.
     */
    find(token) {
      if (!token) return null;
      if (this.declarations.has(token)) {
        return this.declarations.get(token);
      }
      if (token.includes('.')) {
        // `SortedGT.sort_toFinset` → `List.SortedGT.sort_toFinset` (qualifiers compare
        // case-insensitively, as in dot notation); never fall back to the bare short name,
        // which may belong to a sibling (`List.SortedLT.sort_toFinset`).
        const want = token.split('.');
        for (const decl of this.declarations.values()) {
          const have = decl.name.replace(/^_root_\./, '').split('.');
          if (have.length < want.length) continue;
          const tail = have.slice(have.length - want.length);
          if (tail[tail.length - 1] === want[want.length - 1] &&
              tail.slice(0, -1).every((seg, k) => seg.toLowerCase() === want[k].toLowerCase())) {
            return decl;
          }
        }
        return null;
      }
      return null;
    }

    /**
     * Scan all Lean diff files on the current GitHub page.
     */
    scanPage() {
      if (this.isScanning) return;
      this.isScanning = true;

      try {
        // Query file containers (classic, split, and new React /changes view)
        let fileContainers = document.querySelectorAll(
          '.file, .js-file, [data-details-container-group="file"], [data-file-type=".lean"], ' +
          '[data-component="diff-file"], [data-tag="diff-entry"], section[data-file-path], ' +
          'div[data-file-path]'
        );
        // Newer /changes view: one labelled region per file.
        if (fileContainers.length === 0) {
          fileContainers = document.querySelectorAll('[role="region"][aria-labelledby]');
        }

        let filesFound = 0;
        fileContainers.forEach((fileEl) => {
          const filePath = this.extractFilePath(fileEl);
          // If ends with .lean or in Mathlib PR
          if (filePath && (filePath.endsWith('.lean') || !filePath.includes('.'))) {
            filesFound++;
            this.scanDiffLines(fileEl, filePath);
          }
        });

        // Fallback: scan any diff lines on page if file containers are nested differently
        if (filesFound === 0) {
          const allDiffContainers = document.querySelectorAll(
            '.diff-table, table.highlight, [data-component="diff-lines"], .js-diff-progressive-container, table[role="grid"]'
          );
          allDiffContainers.forEach((container) => {
            this.scanDiffLines(container, 'PR_Diff.lean');
          });
        }

        this.scannedFileCount = filesFound;
        this.lastScanTime = Date.now();
      } catch (err) {
        console.warn('[Lean Lens] Error scanning PR diff:', err);
      } finally {
        this.isScanning = false;
      }
    }

    /**
     * Extract file path from GitHub file header or attributes.
     */
    extractFilePath(fileEl) {
      if (!fileEl) return '';

      // Direct attribute
      const pathAttr = fileEl.getAttribute('data-file-path') || fileEl.getAttribute('data-path');
      if (pathAttr) return pathAttr;

      // Labelled region (newer /changes view): the label is the file header.
      const labelId = fileEl.getAttribute('aria-labelledby');
      const label = labelId && document.getElementById(labelId);
      if (label) return label.textContent.replace(/[\u200e\u200f]/g, '').trim();

      // Header link
      const header = fileEl.querySelector(
        '[data-component="diff-file-header"], [data-tag="diff-file-header"], ' +
        '.file-header, .file-info, h3, h2'
      );
      if (header) {
        const link = header.querySelector('a[title], a.Link--primary, a.wb-break-all, a');
        if (link) {
          return link.getAttribute('title') || link.textContent.trim();
        }
        return header.textContent.trim().split('\n')[0].trim();
      }

      return '';
    }

    /**
     * Scan line by line for Lean 4 declarations and docstrings.
     */
    scanDiffLines(container, filePath) {
      // One selector per view, so a line is never read twice (row + cell) and line
      // numbers / markers in sibling cells don't leak into the text.
      const LINE_SELECTORS = [
        '.diff-text-inner', '.blob-code-inner', '[data-tag="diff-line"]',
        '[data-component="diff-line"]', '.react-code-text', 'td.blob-code'
      ];
      let rows = [];
      for (const sel of LINE_SELECTORS) {
        const found = container.querySelectorAll(sel);
        if (found && found.length) { rows = Array.from(found); break; }
      }
      rows = rows.filter(row => !this.isDeletedLine(row));
      if (rows.length === 0) return;

      let currentDocstring = '';
      let inDocstring = false;

      const textOf = (row) => (row.textContent || '').replace(/^[+\s]/, '').trimEnd();
      const vscope = new VariableScope();
      const lineAt = (j) => (j < rows.length ? textOf(rows[j]) : null);

      for (let i = 0; i < rows.length; i++) {
        const row = rows[i];
        let lineText = textOf(row);

        // Check for docstring delimiters /-- and -/
        if (lineText.includes('/--')) {
          inDocstring = true;
          currentDocstring = lineText.substring(lineText.indexOf('/--') + 3).trim();
          if (lineText.includes('-/')) {
            inDocstring = false;
            currentDocstring = currentDocstring.replace(/-\/.*$/, '').trim();
          }
          continue;
        } else if (inDocstring) {
          if (lineText.includes('-/')) {
            inDocstring = false;
            const endPart = lineText.substring(0, lineText.indexOf('-/')).trim();
            if (endPart) currentDocstring += '\n' + endPart;
          } else {
            currentDocstring += '\n' + lineText.trim();
          }
          continue;
        }

        let trimmed = lineText.trim();
        const scoped = trackScope(vscope, trimmed, lineAt, i);
        if (scoped) {
          i += scoped.skip;
          if (!scoped.rest) continue;
          trimmed = scoped.rest; // `variable {L} in theorem …` on one line
        }
        const match = trimmed.match(DECL_REGEX);
        if (!match && OTHER_COMMAND.test(trimmed)) vscope.declared();
        if (match) {
          const kind = match[1];
          const name = match[2];
          let rest = match[3] || '';

          // Signatures often span lines: keep reading until `:=`, `where`, `|` or ` by`.
          let j = i + 1;
          // (An `alias` is one line: its signature can't be told apart from the next command.)
          for (; kind !== 'alias' && j < rows.length && j <= i + 15 && signatureEnd(rest, false) === -1; j++) {
            rest += '\n' + textOf(rows[j]);
          }
          const sigEnd = signatureEnd(rest, kind === 'alias');
          let body = (sigEnd !== -1 ? rest.substring(0, sigEnd) : rest).replace(/\s+/g, ' ').trim();
          // With the section variables it takes (`gelfandRadiusNorm (K : Type u_1) (L : Type u_2) … (x : L)`).
          if (kind !== 'alias') {
            const theorem = /^(theorem|lemma)$/.test(kind);
            body = withVariables(vscope.variablesFor(kind, body, theorem ? '' : bodyAfter(rest, sigEnd, lineAt, j)), body);
          }
          vscope.declared();
          const signature = leanStyle(kind, name, body, (n) => { const d = this.declarations.get(n); return d && kind !== 'alias' ? d.signature : null; });

          const lineNum = this.extractLineNumber(row, i + 1);

          const declInfo = {
            protected: /^(?:@\[[^\]]*\]\s*)*(?:\w+\s+)*protected\s/.test(trimmed),
            name: name,
            shortName: name.split('.').pop(),
            kind: kind,
            typeSignature: signature,
            signature: body,
            docstring: currentDocstring || `*Defined locally in this pull request.*`,
            module: filePath,
            filePath: filePath,
            lineNumber: lineNum,
            source: 'pr_diff',
            element: row
          };

          this.declarations.set(name, declInfo);
          if (name.startsWith('_root_.')) this.declarations.set(name.slice(7), declInfo);
          const shortName = declInfo.shortName;
          const exact = declInfo.declaredAs === shortName || name === shortName;
          if (shortName && (!this.declarations.has(shortName) || (exact && this.viaShort.has(shortName)))) {
            this.declarations.set(shortName, declInfo);
            if (exact) this.viaShort.delete(shortName); else this.viaShort.add(shortName);
          }

          currentDocstring = '';
        } else if (trimmed && !trimmed.startsWith('--') && !trimmed.startsWith('/-') && !trimmed.startsWith('@[')) {
          currentDocstring = '';
        }
      }
    }

    /** Paths of every Lean file in the PR on this page, including diffs GitHub shows collapsed. */
    filePaths() {
      let containers = document.querySelectorAll(
        '.file, .js-file, [data-details-container-group="file"], [data-file-type=".lean"], ' +
        '[data-component="diff-file"], [data-tag="diff-entry"], section[data-file-path], div[data-file-path]'
      );
      if (containers.length === 0) containers = document.querySelectorAll('[role="region"][aria-labelledby]');
      const paths = new Set();
      containers.forEach((el) => {
        const p = this.extractFilePath(el);
        if (p && p.endsWith('.lean')) paths.add(p);
      });
      return [...paths];
    }

    /**
     * Declarations in a whole Lean source file, with names qualified by the enclosing
     * `namespace`s, docstrings and multi-line signatures. Used for files fetched at the
     * PR's commit (collapsed diffs, imported project files), so it needs no DOM.
     */
    /**
     * The section variables in scope at `line` (1-based) of a file: [{ name, bi, type }], in
     * order, with `Type*` named as Lean names it there (`s : ι → Type u_8`).
     */
    variablesAt(text, line) {
      const lines = text.split('\n');
      const vscope = new VariableScope();
      const lineAt = (j) => (j < lines.length ? lines[j] : null);
      let comment = 0;
      let declScope = null; // the scope the declaration at `line` started with (`variable … in` too)
      let declStart = -1, declText = '';
      for (let i = 0; i < Math.min(line, lines.length); i++) {
        let t = lines[i].trim();
        if (comment > 0 || t.startsWith('/-')) {
          comment += (t.match(/\/-/g) || []).length - (t.match(/-\//g) || []).length;
          if (comment < 0) comment = 0;
          continue;
        }
        if (!t || t.startsWith('--')) continue;
        if (SCOPE_OPEN.test(t)) { declScope = null; vscope.declared(); vscope.push(); continue; }
        if (/^end\b/.test(t)) { declScope = null; vscope.declared(); vscope.pop(); continue; }
        const scoped = trackScope(vscope, t, lineAt, i);
        if (scoped) {
          declScope = null;
          i += scoped.skip;
          if (!scoped.rest) continue;
          t = scoped.rest;
        }
        if (DECL_REGEX.test(t) || OTHER_COMMAND.test(t)) { declScope = vscope.snapshot(); declStart = i; declText = t; vscope.declared(); }
      }
      const vars = (declScope || vscope).variablesFor('theorem', '', '');
      // Inside a declaration, its own binders come next (`{ι : Type*}` is named after the variables').
      const own = [];
      const m = declScope && declText.match(DECL_REGEX);
      if (m && m[1] !== 'alias') {
        let rest = m[3] || '';
        for (let j = declStart + 1; j < lines.length && j <= declStart + 15 && signatureEnd(rest, false) === -1; j++) rest += '\n' + lines[j];
        const end = signatureEnd(rest, false);
        const header = end !== -1 ? rest.slice(0, end) : rest;
        const binders = header.slice(0, Math.max(0, groupColon(header)));
        for (const g of binderGroups(binders).groups) {
          // An untyped binder (`{ι}`) shadows a variable of that name: its type is unknown.
          if (g.names.length) g.names.forEach(n => own.push({ bi: g.bi, name: n, type: g.type }));
          else if (g.type !== null) own.push({ bi: g.bi, name: null, type: g.type });
        }
      }
      const all = [...vars, ...own];
      const named = universeNamer(all.map(v => v.type));
      return all.map(v => ({ name: v.name, bi: v.bi, type: v.type === null ? null : named(v.type) }));
    }

    scanSource(text, filePath) {
      const lines = text.split('\n');
      const module = filePath.replace(/\.lean$/, '').replace(/\//g, '.');
      const frames = [];
      const decls = [];
      const known = new Map(); // name → signature of the declarations so far
      const vscope = new VariableScope();
      const lineAt = (j) => (j < lines.length ? lines[j] : null);
      let doc = '';
      let inDoc = false;
      let comment = 0;
      for (let i = 0; i < lines.length; i++) {
        let t = lines[i].trim();
        if (inDoc) {
          const end = t.indexOf('-/');
          doc += '\n' + (end === -1 ? t : t.slice(0, end).trim());
          if (end !== -1) inDoc = false;
          continue;
        }
        if (comment === 0 && t.startsWith('/--')) {
          const end = t.indexOf('-/', 3);
          doc = (end === -1 ? t.slice(3) : t.slice(3, end)).trim();
          inDoc = end === -1;
          continue;
        }
        if (comment > 0 || t.startsWith('/-')) {
          comment += (t.match(/\/-/g) || []).length - (t.match(/-\//g) || []).length;
          if (comment < 0) comment = 0;
          continue;
        }
        if (!t || t.startsWith('--')) continue;
        let m = t.match(/^namespace\s+(\S+)/);
        if (m) { frames.push(m[1]); doc = ''; vscope.declared(); vscope.push(); continue; }
        if (/^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|public|private)\s+)*section\b/.test(t)) { frames.push(null); vscope.declared(); vscope.push(); continue; }
        if (/^end\b/.test(t)) { frames.pop(); vscope.declared(); vscope.pop(); continue; }
        const scoped = trackScope(vscope, t, lineAt, i);
        if (scoped) {
          i += scoped.skip;
          if (!scoped.rest) continue;
          t = scoped.rest; // `variable {L} in theorem …` on one line
        }
        m = t.match(DECL_REGEX);
        if (!m) {
          if (OTHER_COMMAND.test(t)) vscope.declared();
          if (!t.startsWith('@[')) doc = '';
          continue;
        }
        const kind = m[1];
        const declared = m[2];
        let rest = m[3] || '';
        let j = i + 1;
        for (; kind !== 'alias' && j < lines.length && j <= i + 15 && signatureEnd(rest, false) === -1; j++) rest += '\n' + lines[j];
        const sigEnd = signatureEnd(rest, kind === 'alias');
        let body = (sigEnd !== -1 ? rest.substring(0, sigEnd) : rest).replace(/\s+/g, ' ').trim();
        if (kind !== 'alias') {
          const theorem = /^(theorem|lemma)$/.test(kind);
          body = withVariables(vscope.variablesFor(kind, body, theorem ? '' : bodyAfter(rest, sigEnd, lineAt, j)), body);
        }
        vscope.declared();
        const ns = frames.filter(Boolean).join('.');
        const name = declared.startsWith('_root_.') ? declared.slice(7) : (ns ? `${ns}.${declared}` : declared);
        decls.push({
          name, declaredAs: declared, shortName: declared.split('.').pop(), kind,
          protected: /^(?:@\[[^\]]*\]\s*)*(?:\w+\s+)*protected\s/.test(t),
          typeSignature: leanStyle(kind, name, body, (n) => known.get(n) || null), signature: body,
          docstring: doc, module, filePath, lineNumber: i + 1, source: 'project'
        });
        if (kind !== 'alias') [name, declared, declared.split('.').pop()].forEach(n => { if (!known.has(n) || n === declared) known.set(n, body); });
        doc = '';
      }
      return decls;
    }

    /**
     * Merge declarations read from fetched files. Ones scanned from the page keep priority
     * (they can jump to the line); a short name keeps the first declaration it was given.
     */
    addDeclarations(list) {
      for (const d of list || []) {
        const keys = [d.name, d.declaredAs, d.declaredAs && d.declaredAs.replace(/^_root_\./, '')];
        for (const k of keys) {
          if (!k) continue;
          const existing = this.declarations.get(k);
          if (existing && existing.element && !this.viaShort.has(k)) {
            // Keep the page's entry (it can jump to the line), but the whole file at the PR's
            // commit knows the `variable`s it takes, which the diff's hunks may not show.
            if (existing.filePath === d.filePath && existing.name === d.declaredAs && d.signature) {
              existing.signature = d.signature;
              existing.typeSignature = d.typeSignature;
            }
            continue;
          }
          this.declarations.set(k, d);
          this.viaShort.delete(k);
        }
        if (d.shortName && !this.declarations.has(d.shortName)) { this.declarations.set(d.shortName, d); this.viaShort.add(d.shortName); }
      }
    }

    /** Deleted lines in classic (`.blob-code-deletion`, marker `-`) and newer (`code.deletion`) views. */
    isDeletedLine(row) {
      if (row.classList && (row.classList.contains('blob-code-deletion') || row.classList.contains('diff-line-deletion'))) {
        return true;
      }
      if (row.getAttribute && row.getAttribute('data-code-marker') === '-') return true;
      return Boolean(row.closest && row.closest('code.deletion, .blob-code-deletion, .diff-line-deletion'));
    }

    /**
     * Extracts the line number from a diff row or attribute.
     */
    extractLineNumber(row, fallback) {
      if (!row) return fallback;
      const cell = row.closest && row.closest('[data-line-number]');
      if (cell) return parseInt(cell.getAttribute('data-line-number'), 10);
      const lineAttr = row.getAttribute('data-line-number') ||
                       row.getAttribute('data-line-number-right') ||
                       row.getAttribute('data-line');
      if (lineAttr) return parseInt(lineAttr, 10);

      const numCell = row.parentElement?.querySelector('td[data-line-number], [data-line-number]');
      if (numCell) {
        const val = numCell.getAttribute('data-line-number');
        if (val) return parseInt(val, 10);
      }

      return fallback;
    }
  }

  // `self` lets the service worker importScripts() this file to scan fetched sources.
  const scope = typeof window !== 'undefined' ? window : self;
  scope.LeanPRScanner = new LeanPRScanner();
})();
