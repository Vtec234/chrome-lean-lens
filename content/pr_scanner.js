/**
 * Lean 4 In-PR Declaration Scanner.
 * Parses Pull Request diffs and commit changes on GitHub to index newly defined
 * theorems, lemmas, definitions, and structures directly within the PR!
 * Supports classic diffs and the new React-based /changes PR interface.
 */

(function () {
  // `theorem foo …`, with attributes and modifiers; group 1 = kind, 2 = name, 3 = the rest.
  const DECL_REGEX = /^(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|public\s+|noncomputable\s+|scoped\s+|partial\s+|nonrec\s+|unsafe\s+|meta\s+)*(theorem|lemma|def|inductive|structure|class|abbrev|opaque|instance|alias)\s+([A-Za-z0-9_'.\u0370-\u03FF\u2070-\u209F]+)([\s\S]*)/;
  /**
   * A declaration's signature as Lean's hover prints it (`foo (x : ℝ) : P`); aliases as written.
   * `known(name)`: signatures of the declarations before it (for `(tprod R) f` coercions).
   */
  function leanStyle(kind, name, body, known = null) {
    const bc = (typeof window !== 'undefined' ? window : self).VersoBinderContext;
    if (kind === 'alias' || !bc || !bc.leanSignature) return `${kind} ${name}${body ? ' ' + body : ''}`;
    // (One declaration Lean's printing can't be emulated on must not stop a file's scan.)
    try { return bc.leanSignature(name, body, known); } catch (err) { return `${name}${body ? ' ' + body : ''}`; }
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
  Object.setPrototypeOf(OUT_PARAM_CLASSES, null); // looked up by words from the source: no `constructor`, `toString`, … from Object

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
     * not theorems). `known(name)`: the signature of a declaration of the file, if any.
     */
    variablesFor(kind, header, body, known = null) {
      const frames = this.pending ? [...this.frames, this.pending] : this.frames;
      const all = frames.flatMap(f => f.vars);
      if (!all.length) return [];
      const updates = frames.flatMap(f => f.updates);
      // The variable `name` means at `seq`: the latest declared before it.
      const byName = new Map();
      all.forEach((v, k) => { if (v.name) { if (!byName.has(v.name)) byName.set(v.name, []); byName.get(v.name).push(k); } });
      const at = (name, seq) => {
        const ks = byName.get(name);
        if (ks) for (let j = ks.length - 1; j >= 0; j--) if (all[ks[j]].seq < seq) return ks[j];
        return -1;
      };
      const omitted = new Set();
      for (const o of frames.flatMap(f => f.omits)) {
        if (o.name) { const k = at(o.name, o.seq); if (k !== -1) omitted.add(k); }
        else all.forEach((v, k) => { if (v.bi === '[' && v.seq < o.seq && norm(v.type) === o.type) omitted.add(k); });
      }
      // (A variable's names are read once: `v.names`.)
      const deps = all.map((v, k) => [...(v.names = v.names || namesOf(v.type))].map(n => at(n, v.seq)).filter(j => j !== -1 && j !== k));
      const biOf = (k) => {
        let best = null;
        for (const u of updates) if (u.name === all[k].name && u.seq > all[k].seq && at(u.name, u.seq) === k && (!best || u.seq > best.seq)) best = u;
        return best ? best.bi : all[k].bi;
      };
      // Names the declaration uses free, minus its own binders (which shadow variables).
      const bc = (typeof window !== 'undefined' ? window : self).VersoBinderContext;
      // (No top-level colon, as in `structure S (x : α) where`: all of it is binders.)
      const colon = groupColon(header);
      const own = new Set(binderGroups(colon === -1 ? header : header.slice(0, colon)).groups.flatMap(g => g.names));
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
      // (A definition or structure takes only the instances it uses: Lean drops its unused
      // variables. See `instanceUsed`.)
      const theorem = /^(theorem|lemma)$/.test(kind);
      const code = theorem ? '' : stripComments(counted);
      for (let changed = true; changed;) {
        changed = false;
        all.forEach((v, k) => {
          if (chosen.has(k) || omitted.has(k) || v.bi !== '[') return;
          if ((deps[k].every(j => chosen.has(j)) && (theorem || instanceUsed(v.type, code, known))) || needs(v, k)) { add(k); changed = true; }
        });
      }
      // A variable shadowed by a later one prints as `s✝`, in its binder and where it is used.
      const shadowed = (k) => Boolean(all[k].name) && byName.get(all[k].name)[byName.get(all[k].name).length - 1] > k;
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

  // Instances a definition or structure may have in scope without using them (Lean then leaves
  // them out), each with the signs of use that keep it: algebra's instances are nearly always
  // used, so only these need one (`def Blocked (T : ι → Rectangle) … : Prop` has no `[Fintype ι]`).
  const INSTANCE_USES = {
    Fintype: /\b(?:Fintype|Finite|univ|card|det|trace|mulVec|vecMul|dotProduct|toMatrix|Matrix|elems|piFinset)\b|[∑∏⨁]\s*[^,∈]*,|⬝ᵥ|\*ᵥ|ᵥ\*|!!\[/,
    Finite: /\b(?:Finite|Fintype|card|toFinset|finite)\b/,
    DecidableEq: /\b(?:Decidable\w*|update|insert|erase|if|decide|filter|image|toFinset|dedup|biUnion|single|swap|Perm|det|diagonal|Matrix|sdiff|symmDiff|cycleType|support|piFinset)\b|[∪∩∆\\]|\{[^{}|]*,[^{}|]*\}/,
    DecidablePred: /\b(?:Decidable\w*|if|decide|filter|count|find|takeWhile|dropWhile|partition)\b|\{[^{}|]*\|/,
    DecidableRel: /\b(?:Decidable\w*|if|decide|filter|sort|insertionSort|mergeSort|max|min)\b/,
    Nonempty: /\b(?:Nonempty|default|arbitrary|choice|choose|Classical)\b/,
    Inhabited: /\b(?:Inhabited|default|arbitrary)\b|!/,
    Countable: /\b(?:Countable|encode)\b/,
    Encodable: /\b(?:Encodable|encode|decode)\b/,
    Infinite: /\bInfinite\b/,
    Unique: /\b(?:Unique|default|uniq)\b/,
    IsEmpty: /\b(?:IsEmpty|elim)\b/
  };
  Object.setPrototypeOf(INSTANCE_USES, null);

  /**
   * Might a definition whose text is `code` use an instance of type `type`? Also when it uses a
   * declaration of the file that takes one (`f.map …` with `map [Nonempty ι] …`).
   */
  function instanceUsed(type, code, known = null) {
    const head = ((type || '').trim().match(/^[\w.']+/) || [''])[0].split('.').pop();
    const uses = INSTANCE_USES[head];
    if (!uses || uses.test(code)) return true;
    if (!known) return false;
    const takes = new RegExp(`\\[(?:[^\\]:]*:\\s*)?(?:[\\w.]*\\.)?${head}\\b`);
    for (const word of new Set(code.match(/[A-Za-z_][\w'.]*/g) || [])) {
      const sig = known(word) || (word.includes('.') ? known(word.split('.').pop()) : null);
      if (sig && takes.test(sig)) return true;
    }
    return false;
  }

  /** Text without `--` and `/- … -/` comments (docstrings too). */
  function stripComments(text) {
    return (text || '').replace(/\/-[\s\S]*?-\//g, ' ').replace(/--.*$/gm, ' ');
  }

  /**
   * `structure S (x : α) where …` without a type is a `Type`, as Lean infers it when no
   * universe is in sight (none in its binders, no `Type`/`Sort` in its fields).
   */
  function withInferredSort(kind, body, after) {
    if (!/^(structure|class|inductive)$/.test(kind) || groupColon(body) !== -1 || /\bextends\b/.test(body)) return body;
    if (/\bSort\b|\bType\s*[*_]|\bType\s+[\w(]/.test(body) || /\b(?:Type|Sort)\b/.test(stripComments(after))) return body;
    return `${body} : Type`.trim();
  }

  const CLOSE_OF = { '(': ')', '{': '}', '[': ']', '⦃': '⦄' };
  Object.setPrototypeOf(CLOSE_OF, null);

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

  // `#doc (Manual) "Title" =>`: a Verso document (a blueprint chapter), prose to the end of the file.
  const VERSO_DOC = /^#doc\b/;

  /**
   * Where a Verso document starts and the ```lean blocks in it: { docLine, fences: [[open,
   * close], …] }, 1-based (code lines are strictly between a fence's lines; docLine 0: none).
   */
  function versoRegions(text) {
    const lines = text.split('\n');
    const at = lines.findIndex(l => VERSO_DOC.test(l));
    if (at === -1) return { docLine: 0, fences: [] };
    const fences = [];
    let open = null;
    for (let k = at + 1; k < lines.length; k++) {
      const m = lines[k].match(/^\s*(`{3,})(.*)$/);
      if (!m) continue;
      if (!open) open = { at: k, ticks: m[1].length, lean: /^\s*lean\b/.test(m[2]) };
      else if (m[1].length >= open.ticks && !m[2].trim()) { if (open.lean) fences.push([open.at + 1, k + 1]); open = null; }
    }
    if (open && open.lean) fences.push([open.at + 1, lines.length + 1]);
    return { docLine: at + 1, fences };
  }

  /**
   * The fields of a `structure … where` whose `where` is on line `whereLine`: each as the
   * projection Lean declares, `S.f {params} (self : S params) : T` (earlier fields in `T` read
   * `self.g`). `vars` are the section variables the structure takes (`variablesFor`): its first
   * parameters. [{ field, decl }].
   */
  function structureFields(lines, whereLine, header, name, vars, known = null, declLine = whereLine) {
    const indentOf = (l) => (l.match(/^\s*/) || [''])[0].length;
    // (Fields are indented past the `structure` line; `    Prop where` may be indented too.)
    const base = indentOf(lines[declLine] || '');
    // The structure's parameters (its variables first), implicit in each projection.
    const colon = groupColon(header);
    const params = binderGroups(colon === -1 ? header : header.slice(0, colon)).groups.filter(g => g.type !== null);
    const implicit = params.map(g => g.bi === '[' ? `[${g.type}]` : `{${g.names.join(' ')} : ${g.type}}`).join(' ');
    const taken = (vars || []).filter(v => v.included);
    const asImplicit = taken.map(v => Object.assign({}, v, { bi: v.bi === '[' ? '[' : '{' }));
    const explicitNames = [...taken.filter(v => v.bi === '(').map(v => v.name), ...params.filter(g => g.bi === '(').flatMap(g => g.names)];
    const applied = [name.split('.').pop(), ...explicitNames].join(' ');
    const out = [];
    const seen = [];
    const selfTypes = new Map(); // `self.g` → the type of an earlier field `g`
    const typeOf = (n) => selfTypes.get(n) || (known ? known(n) : null);
    let doc = '';
    for (let k = whereLine + 1; k < lines.length; k++) {
      const raw = lines[k];
      if (!raw.trim()) continue;
      if (indentOf(raw) <= base && !/^\s*\/--/.test(raw)) break;
      const t = raw.trim();
      if (t.startsWith('/--')) {
        const end = t.indexOf('-/');
        doc = (end === -1 ? t.slice(3) : t.slice(3, end)).trim();
        for (let q = k + 1; end === -1 && q < lines.length; q++) { const e = lines[q].indexOf('-/'); doc += ' ' + (e === -1 ? lines[q] : lines[q].slice(0, e)).trim(); k = q; if (e !== -1) break; }
        continue;
      }
      if (/^(--|deriving\b|[A-Za-z_][\w']*\s*::\s*$)/.test(t)) continue; // comments, `deriving`, `mk ::`
      const m = t.match(/^\(?([^\s:()]+(?:\s+[^\s:()]+)*)\s*:\s*([\s\S]*?)\)?$/);
      if (!m || /[^\w'\s\u0370-\u03FF\u2080-\u209C]/.test(m[1])) continue;
      let type = m[2];
      // The type continues on deeper lines; a default value `:= …` isn't part of it.
      for (let q = k + 1; q < lines.length && lines[q].trim() && indentOf(lines[q]) > indentOf(raw); q++) { type += ' ' + lines[q].trim(); k = q; }
      type = type.replace(/\s*:=[\s\S]*$/, '').trim();
      if (!type) continue;
      let shown = type;
      seen.forEach(g => { shown = shown.replace(new RegExp(`(?<![\\w'.])${g.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}(?![\\w'])`, 'g'), `self.${g}`); });
      for (const field of m[1].split(/\s+/)) {
        const own = `${implicit ? implicit + ' ' : ''}(self : ${applied}) : ${shown}`.trim();
        const sig = withVariables(asImplicit, own);
        out.push({ field, decl: { name: `${name}.${field}`, typeSignature: leanStyle('def', `${name}.${field}`, sig, typeOf), signature: sig, docstring: doc || `Field \`${field}\` of \`${name}\`.`, lineNumber: k + 1 } });
        seen.push(field);
        selfTypes.set(`self.${field}`, shown);
      }
      doc = '';
    }
    return out;
  }

  /**
   * The body of a `def … : Prop := body` (what `intro` sees through), when it is short and on
   * the declaration's lines; else null.
   */
  function propValue(kind, signature, after) {
    if (!/^(def|abbrev)$/.test(kind) || !/:\s*Prop\s*$/.test(signature) || !/^\s*:=/.test(after || '')) return null;
    // (`Type*` is `Type u_1`, … as Lean names it in the definition.)
    const v = universeNamer([signature, after])(after.replace(/^\s*:=/, '').replace(/\s+/g, ' ').trim());
    return v && v.length < 300 && !/\b(?:by|match|fun|where)\b/.test(v) ? v : null;
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
      this.variablesCache = new Map(); // file text → Map(line → variables in scope there)
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
        if (!inDocstring && VERSO_DOC.test(lineText)) break; // a Verso document: prose to the end

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
            const after = theorem ? '' : bodyAfter(rest, sigEnd, lineAt, j);
            const knownSig = (n) => { const d = this.declarations.get(n); return d ? d.signature : null; };
            body = withInferredSort(kind, withVariables(vscope.variablesFor(kind, body, after, knownSig), body), after);
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
      // Several lookups come per hover (each name of a term): cached per file text and line.
      let perText = this.variablesCache.get(text);
      if (!perText) {
        perText = new Map();
        this.variablesCache.set(text, perText);
        if (this.variablesCache.size > 4) this.variablesCache.delete(this.variablesCache.keys().next().value);
      }
      if (!perText.has(line)) perText.set(line, this.variablesAtUncached(text, line));
      return perText.get(line);
    }

    variablesAtUncached(text, line) {
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
        if (comment === 0 && !inDoc && VERSO_DOC.test(lines[i])) break; // a Verso document: prose to the end
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
        let after = '';
        let vars = [];
        const header = body;
        if (kind !== 'alias') {
          const theorem = /^(theorem|lemma)$/.test(kind);
          after = theorem ? '' : bodyAfter(rest, sigEnd, lineAt, j);
          vars = vscope.variablesFor(kind, body, after, (n) => known.get(n) || null);
          body = withInferredSort(kind, withVariables(vars, body), after);
        }
        vscope.declared();
        const ns = frames.filter(Boolean).join('.');
        const name = declared.startsWith('_root_.') ? declared.slice(7) : (ns ? `${ns}.${declared}` : declared);
        decls.push({
          name, declaredAs: declared, shortName: declared.split('.').pop(), kind,
          protected: /^(?:@\[[^\]]*\]\s*)*(?:\w+\s+)*protected\s/.test(t),
          typeSignature: leanStyle(kind, name, body, (n) => known.get(n) || null), signature: body,
          value: propValue(kind, body, after),
          docstring: doc, module, filePath, lineNumber: i + 1, source: 'project'
        });
        if (kind !== 'alias') [name, declared, declared.split('.').pop()].forEach(n => { if (!known.has(n) || n === declared) known.set(n, body); });
        // A structure's fields are declarations too: `Rectangle.x₀ (self : Rectangle) : ℝ`.
        if ((kind === 'structure' || kind === 'class') && sigEnd !== -1 && /^\s*where\b/.test(rest.slice(sigEnd))) {
          const whereLine = i + (rest.slice(0, sigEnd + 1).match(/\n/g) || []).length;
          let fields = [];
          try { fields = structureFields(lines, whereLine, header, name, vars, (n) => known.get(n) || null, i); } catch (err) { fields = []; }
          for (const f of fields) {
            decls.push(Object.assign({ declaredAs: `${declared}.${f.field}`, shortName: f.field, kind: 'def', module, filePath, source: 'project' }, f.decl));
          }
        }
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
              existing.value = d.value;
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
  scope.LeanPRScanner.versoRegions = versoRegions;
})();
