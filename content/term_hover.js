/**
 * Hovering inside a term, as Lean's infoview does: the smallest term around the pointer
 * (a gap between a function and its arguments, a bracket, an operator), read from the
 * statement it belongs to (continuation lines included), and its type, worked out from the
 * locals' types and the constants' signatures. Adds its functions to `VersoBinderContext`.
 */

(function () {
  const scope = (typeof window !== 'undefined' ? window : self);
  const {
    LOCAL_NAME, USE_NOT_FN, annotateText, binderParts, displayType, freeNames, group, instantiateSignature,
    isSignature, leadBinderText, matchTerm, parseTerm, piOf, piSort, residualParts, residualSignature,
    showTerm, sortOf, sortText, stripAscriptions, substTerm, tChildren, tCore, tSpan, tWithChildren,
    typeHead, universeParams
  } = scope.LeanTerms;
  const {
    DECL_START, LINE_SELECTORS, ROW_SEL, domLineEls, headerEnd, inferPending, localType, localVariableInfo,
    nearbyRowLines, projectionType, replayChanges
  } = scope.VersoBinderContext.internal;

  /**
   * The statement around the hovered line (`joinStatement`), with `code` as the hovered
   * line's text: { text, lineStart }.
   */
  const statementCache = typeof WeakMap === 'function' ? new WeakMap() : null;

  function statementAround(node, code) {
    const el = node && (node.nodeType === 1 ? node : node.parentElement);
    const key = el && el.closest ? el.closest(`${LINE_SELECTORS.join(', ')}, ${ROW_SEL}`) : null;
    const hit = key && statementCache && statementCache.get(key);
    if (hit && hit.code === code && Date.now() - hit.at < 2000) return hit.result;
    // Only the lines near the hovered one matter: walk the neighbouring rows (cheap on every
    // mouse move), else read the file's lines.
    let d = null;
    try { d = (el && nearbyRowLines(el, 15)) || domLineEls(node); } catch (err) { d = null; }
    let result = { text: code, lineStart: 0 };
    if (d && d.lines) {
      const lines = d.lines.slice();
      lines[d.idx] = code;
      const j = joinStatement(lines, d.idx);
      // Each joined line: its cell (null for the hovered one), where it starts, its length.
      const parts = j.starts.map((start, k) => ({ cell: j.from + k === d.idx ? null : d.cells[j.from + k], start, len: lines[j.from + k].length }));
      result = { text: j.text, lineStart: j.lineStart, parts };
    } else if (d) {
      const from = Math.max(0, d.idx - 15);
      const to = Math.min(d.els.length - 1, d.idx + 15);
      const lines = [];
      for (let i = from; i <= to; i++) lines.push(i === d.idx ? code : d.text(d.els[i]));
      result = joinStatement(lines, d.idx - from);
    }
    if (key && statementCache) statementCache.set(key, { code, at: Date.now(), result });
    return result;
  }

  const GAP_OPEN = '([{⟨', GAP_CLOSE = ')]}⟩';

  // Tactic keywords in front of a term (`exact`, `refine`, `have h :`, …).
  const GAP_LEAD = /^\s*(?:·\s*)?(?:(?:exact|exacts|apply|refine'?|use|exists|existsi|calc|show|change|convert|convert_to|specialize|trans|rcases|have|haveI|let|letI|suffices|replace|from|by|return|then|else|if|using|mod_cast|exact_mod_cast|apply_mod_cast|simpa(?:\s+[^\n]*?\busing)?)(?![\w'!?])\s*)+/;

  // Lines / segments that aren't terms: declarations, and tactics whose arguments are names,
  // patterns or tactic-specific syntax.
  const GAP_NOT_TERM = /^\s*(?:·\s*)?(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|public|noncomputable|scoped|local|partial|nonrec|unsafe|meta)\s+)*(?:theorem|lemma|def|instance|example|abbrev|opaque|structure|class|inductive|axiom|variable|universe|open|namespace|section|end|import|attribute|alias|notation|macro|syntax|set_option|deriving|match|do|intro|intros|rintro|cases|induction|obtain|subst|ext|funext|congr|gcongr|constructor|exfalso|contradiction|norm_num|simp|simp_all|dsimp|simp_rw|rw|rwa|erw|nth_rw|rewrite|field_simp|ring|ring_nf|linarith|nlinarith|polyrith|linear_combination|positivity|omega|decide|aesop|tauto|unfold|delta|clear|revert|generalize|by_contra|by_cases|push_neg|contrapose|filter_upwards|norm_cast|push_cast|split_ifs|interval_cases|fin_cases|choose|lift|wlog|rename_i|set|conv|apply_fun|bound|abel|module|match_scalars|fun_prop|continuity|measurability)(?![\w'!?])/;

  // Top-level separators between terms.
  const GAP_SEP = /^(?:,|:=|;|<;>|=>|↦|←|<-|<\||\|>|\$| : | at | with | using | then | else | from | by | generalizing )/;

  const GAP_NAMES_AFTER = new Set(['at', 'with', 'generalizing']); // what follows is names, not a term

  const GAP_LEAVES = new Set(['id', 'raw', 'named']);

  /** Index of the opener matching the closer at `closeIdx`, or -1. */
  function matchOpenBack(text, closeIdx) {
    for (let i = closeIdx - 1, depth = 0; i >= 0; i--) {
      const ch = text[i];
      if (GAP_CLOSE.includes(ch) || ch === '⦄') depth++;
      else if (GAP_OPEN.includes(ch) || ch === '⦃') { if (depth === 0) return i; depth--; }
    }
    return -1;
  }

  /**
   * Is the bracket at `open` a binder group (`{s y : ℝ}`, `fun (x y : ℝ) =>`, `theorem foo
   * (f g : ℕ → ℕ)`) rather than a term (`(f x : ℝ)` ascribes `f x`)? Looks back over earlier
   * groups and names for a binding keyword.
   */
  function isBinderGroup(text, open) {
    if ('{⦃['.includes(text[open])) return true;
    let j = open;
    for (let guard = 0; guard < 40; guard++) {
      while (j > 0 && /\s/.test(text[j - 1])) j--;
      if (j === 0) return false;
      if (')}]⦄'.includes(text[j - 1])) {
        const o = matchOpenBack(text, j - 1);
        if (o === -1) return false;
        j = o;
        continue;
      }
      const w = text.slice(0, j).match(/([^\s()[\]{}⦃⦄⟨⟩,]+)$/);
      if (!w) return false;
      if (/^(?:fun|λ|∀|∃|∃!|Π|∑|∏|∑'|∏'|⋃|⋂|⨆|⨅|theorem|lemma|def|instance|example|abbrev|opaque|have|let|suffices|obtain|structure|class|inductive)$/.test(w[1])) return true;
      if (!/^[\w'.\u0370-\u03FF\u1F00-\u1FFF\u2080-\u209C!?]+$/.test(w[1])) return false; // `:=`, operators: a term context
      j -= w[1].length;
    }
    return false;
  }

  /** Innermost-first path of nodes whose span contains `off` (empty if none). */
  function pathTo(node, off) {
    const sp = tSpan(node);
    if (!sp || off < sp[0] || off >= sp[1]) return [];
    for (const c of tChildren(node)) {
      const p = pathTo(c, off);
      if (p.length) return p.concat([node]);
    }
    return [node];
  }

  /**
   * The term at `offset` in `text` when the offset isn't on a name (a space, bracket, operator
   * or numeral): { node, parent, src, start, end, text } with `node` parsed from `src` and
   * [start, end) its span in `text`; null where there is no term (names, patterns, tactics).
   * Candidate segments run between top-level separators inside the innermost bracket; the
   * nearest one that parses wins (`∀ x : ℝ, p x` needs its `:` and `,`).
   */
  function termAtOffset(text, offset) {
    if (!text || offset < 0 || offset >= text.length) return null;
    let lo = 0, hi = text.length;
    for (let i = offset - 1, depth = 0; i >= 0; i--) {
      const ch = text[i];
      if (GAP_CLOSE.includes(ch)) depth++;
      else if (GAP_OPEN.includes(ch)) { if (depth === 0) { lo = i + 1; break; } depth--; }
    }
    for (let i = offset, depth = 0; i < text.length; i++) {
      const ch = text[i];
      if (GAP_OPEN.includes(ch)) depth++;
      else if (GAP_CLOSE.includes(ch)) { if (depth === 0) { hi = i; break; } depth--; }
    }
    // The names of a binder group (`{s y : ℝ}`) are being bound, not applied.
    const group = lo > 0 && text.slice(lo, hi).match(/^\s*[^\s:()[\]{}⟨⟩,]+(?:\s+[^\s:()[\]{}⟨⟩,]+)*\s:\s/);
    if (group && offset < lo + group[0].length - 2 && isBinderGroup(text, lo - 1)) return null;
    const seps = [];
    for (let i = lo, depth = 0; i < hi;) {
      const ch = text[i];
      if (GAP_OPEN.includes(ch)) { depth++; i++; continue; }
      if (GAP_CLOSE.includes(ch)) { depth--; i++; continue; }
      const m = depth === 0 && text.slice(i, Math.min(hi, i + 14)).match(GAP_SEP);
      if (m) {
        if (i <= offset && offset < i + m[0].length) return null; // on a separator
        seps.push({ s: i, e: i + m[0].length, v: m[0].trim() });
        i += m[0].length;
        continue;
      }
      i++;
    }
    // Widest candidate first: the parser knows which commas and colons belong to binders
    // (`∑ i ∈ s, f i = 0` is `(∑ i ∈ s, f i) = 0`), and segments that don't parse are skipped.
    const starts = [{ at: lo, after: null }, ...seps.filter(x => x.e <= offset).map(x => ({ at: x.e, after: x.v }))];
    const ends = [hi, ...seps.filter(x => x.s > offset).map(x => x.s).reverse()];
    for (const st of starts) {
      if (GAP_NAMES_AFTER.has(st.after)) return null;
      // A command or tactic (`lift x to ℕ`, `congr 1`) only where one can start; after ` : `
      // or `:=`, `lift φ x` / `congr f x` are terms.
      const tacticPos = (st.at === 0 && lo === 0) || [';', '<;>', 'by'].includes(st.after);
      if (tacticPos && GAP_NOT_TERM.test(text.slice(st.at, hi))) continue;
      for (const en of ends) {
        let a = st.at, b = en;
        const lead = text.slice(a, b).match(GAP_LEAD);
        if (lead) a += lead[0].length;
        while (a < b && /\s/.test(text[a])) a++;
        while (b > a && /\s/.test(text[b - 1])) b--;
        if (offset < a || offset >= b) continue;
        const src = text.slice(a, b);
        // A structure field defined with arguments (`left_inv φ := …`, `{ toFun x := … }`):
        // its name and binders, not a term.
        const next = seps.find(x => x.s === en);
        if (next && next.v === ':=' && (st.after === null || st.after === ',' || st.after === ';') && /^[\w'.\u0370-\u03FF\u2080-\u209C]+(?:\s+(?:[\w'\u0370-\u03FF\u2080-\u209C]+|[({⦃][^(){}⦃⦄]*[)}⦄]))+$/.test(src)) return null;
        const tree = parseTerm(src);
        if (!tree) continue;
        const path = pathTo(tree, offset - a);
        const node = path[0];
        if (!node || (GAP_LEAVES.has(node.k) && !node.paren)) return null;
        const sp = tSpan(node);
        // `have h : T := term`: the declared type is what the whole term is elaborated against.
        let expected = null;
        if (path.length === 1 && st.after === ':=') {
          const assign = seps.find(x => x.e === st.at);
          const colon = assign && seps.find(x => x.v === ':' && x.e <= assign.s);
          if (colon && !seps.some(x => x.v === ':=' && x.s > colon.e && x.s < assign.s)) expected = text.slice(colon.e, assign.s).trim();
        }
        // `(2 : ℝ)` with the segment `2`: the ascription gives the numeral's type.
        const sepAfter = seps.find(x => x.s === en);
        const ascribed = st.at === lo && sepAfter && sepAfter.v === ':' && lo > 0 && text[lo - 1] === '(' && path.length === 1
          ? text.slice(sepAfter.e, hi).trim() : null;
        // On the parentheses of `(x + 1)` Lean describes the parentheses (the type is the same).
        const rel = offset - a;
        const onParens = Boolean(node.pspan && node.span) && (rel < node.span[0] || rel >= node.span[1]);
        return {
          node, parent: path[1] || (ascribed ? { k: 'asc', e: node, ty: parseTerm(ascribed) || { k: 'raw', v: ascribed } } : null),
          path, expected, onParens, src, start: a + sp[0], end: a + sp[1], text: showTerm(stripAscriptions(node))
        };
      }
    }
    return null;
  }

  /**
   * Line `idx` joined with the lines it continues and the lines continuing it (deeper indented,
   * open brackets; not a nested tactic block), so a term broken across lines parses whole.
   * Returns { text, lineStart }: newlines become one space (`;` after a `by` block, which the
   * next line can't continue) and comments become spaces, so offsets on the line carry over.
   */
  function joinStatement(lines, idx, maxSpan = 15) {
    const from = Math.max(0, idx - maxSpan);
    const to = Math.min(lines.length - 1, idx + maxSpan);
    const clean = lines.map((l, i) => (i < from || i > to ? '' : (l || '').replace(/--.*$/, m => ' '.repeat(m.length))));
    const blank = (i) => !clean[i].trim();
    const indent = (i) => (clean[i].match(/^\s*(?:·\s+)?/) || [''])[0].length;
    const fresh = (i) => /^\s*(?:\||case\b|next\b|·)/.test(clean[i]) || DECL_START.test(clean[i]);
    const opens = (i) => /(?:\bby|\bdo|\bwhere|\bwith|\bthen|\belse)\s*$/.test(clean[i]) ||
      (/=>\s*$/.test(clean[i]) && /^\s*(?:\||case\b|next\b|·)/.test(clean[i]));
    const net = (i) => {
      let d = 0;
      for (const ch of clean[i]) { if (GAP_OPEN.includes(ch)) d++; else if (GAP_CLOSE.includes(ch)) d--; }
      return d;
    };
    const startOf = new Map();
    const depthAt = new Map(); // bracket depth at the end of the line, within its statement
    let prev = -1;
    for (let i = from; i <= to; i++) {
      if (blank(i)) continue;
      let cont = false;
      if (prev !== -1 && !fresh(i)) {
        const s0 = startOf.get(prev);
        cont = depthAt.get(prev) > 0 || (!opens(prev) && indent(i) > indent(s0));
      }
      startOf.set(i, cont ? startOf.get(prev) : i);
      depthAt.set(i, Math.max(0, (cont ? depthAt.get(prev) : 0) + net(i)));
      prev = i;
    }
    if (!startOf.has(idx)) return { text: clean[idx] || '', lineStart: 0, from: idx, starts: [0] };
    const s0 = startOf.get(idx);
    let e = idx;
    for (let j = idx + 1; j <= to; j++) {
      if (blank(j)) continue;
      if (startOf.get(j) !== s0) break;
      e = j;
    }
    let text = '';
    let lineStart = 0;
    let lastCode = '';
    const starts = [];
    for (let j = s0; j <= e; j++) {
      // A tactic block ends at the line break; so does a structure field (`map_add' x y := …`
      // on its own line, in `{ … }` or after `where`).
      const field = /^\s*[\w'.\u0370-\u03FF\u2080-\u209C]+(?:\s+[\w'\u0370-\u03FF\u2080-\u209C]+)*\s*:=/.test(clean[j]) && !/(?::=|[({[⟨,])\s*$/.test(lastCode);
      if (j > s0) text += field || (/(^|[^\w'])by(?![\w'])/.test(lastCode) && !/[([{⟨]\s*by\b/.test(lastCode)) ? ';' : ' ';
      if (j === idx) lineStart = text.length;
      starts.push(text.length);
      text += clean[j];
      if (!blank(j)) lastCode = clean[j];
    }
    // `starts[k]`: where line `from + k` begins in `text` (for marking a term on each line).
    return { text, lineStart, from: s0, starts };
  }

  // The declaration whose docstring Lean's hover shows under a term of each notation: the
  // notation's own syntax (`«term_+_»`), or what it stands for when that has the docs.
  const INFIX_DOCS = {
    '+': '«term_+_»', '-': '«term_-_»', '*': '«term_*_»', '/': '«term_/_»', '%': '«term_%_»', '^': '«term_^_»',
    '•': '«term_•_»', '=': '«term_=_»', '≠': '«term_≠_»', '<': '«term_<_»', '>': '«term_>_»', '≤': '«term_≤_»',
    '≥': '«term_≥_»', '∧': '«term_∧_»', '∨': '«term_∨_»', '↔': '«term_↔_»', '∈': '«term_∈_»', '∉': '«term_∉_»',
    '⊆': '«term_⊆_»', '⊂': '«term_⊂_»', '∩': '«term_∩_»', '∪': '«term_∪_»', '\\': '«term_\\_»', '∣': '«term_∣_»',
    '∘': '«term_∘_»', '⊔': '«term_⊔_»', '⊓': '«term_⊓_»', '×': '«term_×_»', '×ˢ': '«term_×ˢ_»',
    '×ℂ': 'Complex.«term_×ℂ_»', "⁻¹'": "Set.«term_⁻¹'_»", "''": 'Set.image', '<|': '«term_<|_»', '|>': '«term_|>_»',
    '∘ₛₗ': 'LinearMap.«term_∘ₛₗ_»', '∘ₗ': 'LinearMap.comp', '≪≫ₗ': 'LinearEquiv.trans',
    '⊗[_]': 'TensorProduct.«term_⊗[_]_»', '⊗ₜ[_]': 'TensorProduct.«term_⊗ₜ[_]_»'
  };
  Object.setPrototypeOf(INFIX_DOCS, null); // looked up by words from the source: no `constructor`, `toString`, … from Object

  const PREFIX_DOCS = { '¬': '«term¬_»', '-': '«term-_»' };
  Object.setPrototypeOf(PREFIX_DOCS, null);

  const POSTFIX_DOCS = { '⁻¹': '«term_⁻¹»', 'ᶜ': '«term_ᶜ»' };
  Object.setPrototypeOf(POSTFIX_DOCS, null);

  /** Name of the declaration whose docstring Lean shows for a hovered term (a `termAtOffset` hit), or null. */
  function notationDocName(hit) {
    const n = hit && hit.node;
    if (!n) return null;
    if (hit.onParens) return 'Lean.Parser.Term.paren';
    switch (n.k) {
      case 'bin': return INFIX_DOCS[n.op] || null;
      case 'pre': return PREFIX_DOCS[n.op] || null;
      case 'post': return POSTFIX_DOCS[n.op] || null;
      case 'abs': return 'abs';
      case 'norm': return '«term‖_‖»';
      case 'proj': return 'Lean.Parser.Term.proj';
      case 'asc': return 'Lean.Parser.Term.typeAscription';
      case 'bind':
        if (n.head === '∑') return 'BigOperators.bigsum';
        if (n.head === '∏') return 'BigOperators.bigprod';
        if (n.head === '⨂[_]') return 'TensorProduct.«term⨂[_]_,_»';
        if (n.head === '⨂ₜ[_]') return 'PiTensorProduct.«term⨂ₜ[_]_,_»';
        // `∀ x ∈ s, …` / `∃ ε > 0, …`: binder predicates have their own notation.
        if ((n.head === '∀' || n.head === '∃') && binderParts(n.binders).op && !/^[({[⦃]/.test(n.binders.trim())) {
          return n.head === '∀' ? 'Lean.«term∀__,_»' : 'Lean.«term∃__,_»';
        }
        return null;
      default: return null;
    }
  }

  const PROP_OPS = new Set(['=', '≠', '<', '>', '≤', '≥', '∈', '∉', '⊆', '⊂', '⊇', '⊃', '∣', '↔', '∧', '∨']);

  const ARITH_OPS = new Set(['+', '-', '*', '/', '%', '∪', '∩', '\\', '⊔', '⊓']);

  const NUMERAL_SIBLING_OPS = new Set(['+', '-', '*', '/', '%', '⊔', '⊓', '=', '≠', '<', '>', '≤', '≥']);

  const NOTATION_TYPES = { 'π': 'ℝ', 'Complex.I': 'ℂ' }; // `π` is `Real.pi` (open Real)
  Object.setPrototypeOf(NOTATION_TYPES, null);

  const TYPE_SORTS = {
    'ℕ': 'Type', 'ℤ': 'Type', 'ℚ': 'Type', 'ℝ': 'Type', 'ℂ': 'Type', 'Nat': 'Type', 'Int': 'Type', 'Rat': 'Type',
    'Real': 'Type', 'Complex': 'Type', 'Bool': 'Type', 'Prop': 'Type', 'True': 'Prop', 'False': 'Prop'
  };
  Object.setPrototypeOf(TYPE_SORTS, null);

  const COMP_SIG = '{α : Sort u} {β : Sort v} {δ : Sort w} (f : β → δ) (g : α → β) : α → δ';

  /**
   * A term as Lean prints it after elaboration: ascriptions are gone, and a local ascribed a
   * different type is coerced (`(n : ℝ)` with `n : ℕ` prints as `↑n`).
   */
  function termDisplay(node, text, coerced = null, binders = null) {
    let n = coerced && coerced.size ? withCoercions(node, coerced) : node;
    if (binders && binders.size) n = withBinderTypes(n, binders, node);
    return showTerm(stripAscriptions(n, text || ''));
  }

  /** Binders whose types `termTypeOf` worked out, printed with them (`(i : ι) → …`). */
  function withBinderTypes(n, binders, orig) {
    if (!n || typeof n !== 'object') return n;
    const info = binders.get(orig);
    const kids = tChildren(n), origKids = tChildren(orig || {});
    let m = tWithChildren(n, kids.map((c, i) => withBinderTypes(c, binders, origKids[i])));
    if (info && m.k === 'bind') m = info.arrow ? { k: 'bind', head: 'Π', arrow: true, binders: info.binders, sep: '→', body: m.body } : Object.assign({}, m, { binders: info.binders });
    return m;
  }

  /** `tprod R f` where `tprod R` is a bundled map: `(tprod R) f`, as Lean prints the coercion. */
  function withCoercions(n, coerced) {
    if (!n || typeof n !== 'object') return n;
    let m = tWithChildren(n, tChildren(n).map(c => withCoercions(c, coerced)));
    if (n.k === 'app' && coerced.has(n)) {
      const k = coerced.get(n);
      const named = m.args.filter(a => a.k === 'named').length;
      const at = k + named;
      if (at > 0 && at < m.args.length) {
        m = Object.assign({}, m, { f: Object.assign({ k: 'app', f: m.f, args: m.args.slice(0, at) }, { coeFn: true }), args: m.args.slice(at) });
      } else if (at === 0 && m.f.k === 'app') m = Object.assign({}, m, { f: Object.assign({}, m.f, { coeFn: true }) });
    }
    return m;
  }

  const NUMBER_TOWER = ['ℕ', 'ℤ', 'ℚ', 'ℝ', 'ℂ'];

  const NUMBER_ALIASES = { Nat: 'ℕ', Int: 'ℤ', Rat: 'ℚ', Real: 'ℝ', Complex: 'ℂ' };
  Object.setPrototypeOf(NUMBER_ALIASES, null);

  /** One type for operands of these types: all equal, or the widest of ℕ ⊆ ℤ ⊆ ℚ ⊆ ℝ ⊆ ℂ. */
  function widestType(types) {
    const norm = types.map(t => { const s = t.replace(/\s+/g, ' ').trim(); return NUMBER_ALIASES[s] || s; });
    if (norm.every(t => t === norm[0])) return norm[0];
    const ranks = norm.map(t => NUMBER_TOWER.indexOf(t));
    return ranks.every(r => r >= 0) ? NUMBER_TOWER[Math.max(...ranks)] : null;
  }

  /** Is `type` a proposition (so a value of it is a proof, not a number)? */
  function isPropType(type) {
    const n = tCore(parseTerm(type || ''));
    if (!n) return false;
    if (n.k === 'bin') return PROP_OPS.has(n.op) || n.op === '→';
    if (n.k === 'pre') return n.op === '¬';
    if (n.k === 'bind') return ['∀', '∃', '∃!'].includes(n.head);
    return n.k === 'id' && (n.v === 'True' || n.v === 'False');
  }

  /**
   * Type of a term from `termAtOffset`, as Lean's hover shows it. Locals use their written or
   * inferred types (with `rw … at` replayed), constants `sigOf(name)` (PR declarations,
   * Loogle); `x.f` is generalized field notation. `hint.parent` types numerals from their
   * neighbours (`x + 1`, `x ^ 2`). Resolves to the type text, or null when it can't be told.
   */
  async function termTypeOf(node, src, text, sigOf, hint = {}) {
    let budget = 80;
    const srcOf = (n) => { const sp = tSpan(n); return sp ? src.slice(sp[0], sp[1]) : showTerm(n); };
    const lookup = async (name) => {
      if (!sigOf || --budget < 0) return null;
      try { return universeParams((await sigOf(name)) || null); } catch (err) { return null; }
    };

    const selfType = (() => {
      const m = text.match(/^\s*(?:(?:private|protected|public|noncomputable)\s+)*inductive\s+([^\s(:{[⦃]+)/);
      if (!m) return null;
      const hdr = headerEnd(text);
      if (hdr <= 0 || text[hdr] !== ':') return null;
      const rest = text.slice(hdr + 1);
      const end = rest.search(/\swhere\b|\n\s*\||:=/);
      const type = (end === -1 ? rest : rest.slice(0, end)).replace(/\s+/g, ' ').trim();
      return type ? { name: m[1], type } : null;
    })();
    // Is the hovered line (the end of `text`) in a `variable` command?
    const commandStart = (text.match(/(?:^|\n)(\S[^\n]*)(?:\n(?:[ \t][^\n]*)?)*$/) || [])[1] || '';
    const inVariableCommand = /^variable\b/.test(commandStart);
    // A local's current type; `undefined` when `name` isn't a local, null when it is one whose
    // type can't be told (untyped, or changed by a tactic we can't replay).
    const localSig = async (name) => {
      if (!LOCAL_NAME.test(name)) return undefined;
      if (hint.variableOf && inVariableCommand && --budget >= 0) {
        // Hovering in a `variable` command: Lean's view of the variables there (`Type u_8`).
        let v = null;
        try { v = await hint.variableOf(name); } catch (err) { v = null; }
        if (v) return v;
      }
      const info = localVariableInfo(name, text);
      if (!info) {
        // A file-level `variable` (`[hT : Fact (0 < T)]`), when the caller can read the file.
        let v = null;
        if (hint.variableOf && --budget >= 0) { try { v = await hint.variableOf(name); } catch (err) { v = null; } }
        return v || undefined;
      }
      const prefix = `${name} : `;
      let type = info.typeSignature && info.typeSignature.startsWith(prefix) ? info.typeSignature.slice(prefix.length) : null;
      if (info.inferNeeded) {
        let r = null;
        try { r = await inferPending(info.inferNeeded, text, sigOf, hint.variableOf); } catch (err) { r = null; }
        type = r && r.typeSignature.startsWith(prefix) ? r.typeSignature.slice(prefix.length) : null;
      }
      if (!type || type === '_') return null;
      if (/\b(?:Type|Sort)\*/.test(type) && hint.variableOf && --budget >= 0) {
        // A section variable read from the text (`{s : ι → Type*}`): Lean's universe names.
        let v = null;
        try { v = await hint.variableOf(name); } catch (err) { v = null; }
        if (v && v.replace(/\b(Type|Sort) u_\d+\b/g, '$1*').replace(/\s+/g, ' ') === type.replace(/\s+/g, ' ')) type = v;
      }
      if (info.replay) {
        let res = null;
        try { res = await replayChanges(info.replay.baseType || type, info.replay.changes, text, sigOf); } catch (err) { res = null; }
        if (!res || res.stoppedAt || res.failedAt) return null;
        type = res.type;
      }
      return type;
    };

    // `recv.field`: the field of the receiver's type's namespace (or a numeric projection).
    const fieldSig = async (recvSig, recvText, field) => {
      const r = residualParts(recvSig, [], {}, text);
      if (!r) return null;
      const recvType = showTerm(piOf(r.rest, r.concl));
      if (/^\d+$/.test(field)) {
        if (r.rest.length) return null;
        const p = projectionType(recvType, Number(field));
        return p && p.type && p.type !== '_' ? `${leadBinderText(r.lead)} : ${p.type}`.trim() : null;
      }
      const resolveVar = (v) => {
        const b = r.lead.find(x => x.name === v);
        const t = b ? (b.type ? showTerm(b.type) : null) : localType(v, text);
        return t ? typeHead(t, null) : null;
      };
      const ns = r.rest.length ? 'Function' : typeHead(recvType, resolveVar);
      if (!ns) return null;
      const fsig = await lookup(`${ns}.${field}`);
      const instances = fsig && /RingHom(?:InvPair|CompTriple)/.test(fsig) ? await instancesIn() : null;
      return fsig ? residualSignature(fsig, [], {}, text, { receiver: { term: recvText, type: recvType, binders: r.lead }, instances }) : null;
    };
    const fieldChain = async (sig, recvText, fields) => {
      for (const f of fields) {
        if (!sig) return null;
        sig = await fieldSig(sig, recvText, f);
        recvText = `${recvText}.${f}`;
      }
      return sig;
    };

    const idSig = async (v) => {
      // In an inductive's own constructors its parameters are fixed: `Eqv x y` there takes only
      // the indices of `inductive Eqv : A → A → Prop`.
      if (selfType && (v === selfType.name || v === selfType.name.split('.').pop())) return selfType.type;
      if (Object.prototype.hasOwnProperty.call(TYPE_SORTS, v)) return TYPE_SORTS[v];
      if (Object.prototype.hasOwnProperty.call(NOTATION_TYPES, v)) return NOTATION_TYPES[v];
      if (/^\?/.test(v) || v === '_' || v === '·') return null;
      const segs = v.split('.');
      const local = await localSig(segs[0]);
      if (local !== undefined) return local === null ? null : segs.length === 1 ? local : fieldChain(local, segs[0], segs.slice(1));
      if (segs.length === 1 && /^[a-z]['\w]?$/.test(v)) return null; // a short unbound name: a bound variable
      const sig = await lookup(v);
      if (sig) return sig;
      // `abs_le.mp`, `Set.mem_Icc.1`: a constant followed by fields.
      for (let k = segs.length - 1; k >= 1; k--) {
        if (!/^[a-z_]/.test(segs[k - 1])) continue; // a namespace, not a term
        const base = await lookup(segs.slice(0, k).join('.'));
        if (base) return fieldChain(base, segs.slice(0, k).join('.'), segs.slice(k));
      }
      return null;
    };

    // Signature (a type, possibly with leading binders) of a term.
    const sigOfTerm = async (n) => {
      if (!n || --budget < 0) return null;
      switch (n.k) {
        case 'asc': return showTerm(n.ty);
        case 'id': return idSig(n.v);
        case 'proj': {
          const recv = await sigOfTerm(n.e);
          return recv ? fieldSig(recv, srcOf(n.e), n.f) : null;
        }
        case 'app': {
          const fSig = await sigOfTerm(n.f);
          if (!fSig) return null;
          const { positional, named, argTypes } = await argsOf(n);
          const onCoerce = hint.coerced ? (k) => hint.coerced.set(n, k) : null;
          const instances = /RingHom(?:InvPair|CompTriple)/.test(fSig) ? await instancesIn() : null;
          return residualSignature(fSig, positional, named, text, { argTypes, valueTypes: await valueTypesOf(argTypes), onCoerce, instances });
        }
        case 'bin': {
          if (n.op === '<|' || n.op === '|>') {
            // `f <| x` / `x |> f` is `f x`.
            const [fn, arg] = n.op === '<|' ? [n.l, n.r] : [n.r, n.l];
            const fSig = await sigOfTerm(fn);
            return fSig ? residualSignature(fSig, [srcOf(arg)], {}, text, { argTypes: [await typeOf(arg)] }) : null;
          }
          if (PROP_OPS.has(n.op)) return 'Prop';
          if (n.op === '→') {
            // A function type: `A → P : Prop` for a proposition `P`; else `Sort (imax u v)`.
            const r = await typeOf(n.r);
            if (r === 'Prop') return r;
            return sortOf(parseTerm(r || '')) ? piSort(await typeOf(n.l), r) : null;
          }
          if (n.op === '×' || n.op === '⊕') {
            // `α × β : Type (max u v)`, `α ⊕ β` too.
            const [l, r] = [sortOf(parseTerm((await typeOf(n.l)) || '')), sortOf(parseTerm((await typeOf(n.r)) || ''))];
            if (!l || !r || l.kind !== 'Type' || r.kind !== 'Type' || !l.level || !r.level) return null;
            return sortText('Type', { k: 'app', f: { k: 'id', v: 'max' }, args: [l.level, r.level] });
          }
          if (n.op === "⁻¹'" || n.op === "''") {
            // Preimage `f ⁻¹' s : Set α`, image `f '' s : Set β`, for `f : α → β`.
            const f = parseTerm((await typeOf(n.l)) || '');
            if (!f || f.k !== 'bin' || f.op !== '→') return null;
            return `Set ${showTerm(n.op === "''" ? f.r : f.l, 1025)}`;
          }
          if (n.op === '×ℂ') return 'Set ℂ';
          if (n.op === '×ˢ') {
            const [l, r] = [parseTerm((await typeOf(n.l)) || ''), parseTerm((await typeOf(n.r)) || '')];
            const elem = (t) => (t && t.k === 'app' && t.f.k === 'id' && t.f.v === 'Set' && t.args.length === 1 ? t.args[0] : null);
            return elem(l) && elem(r) ? `Set (${showTerm(elem(l), 36)} × ${showTerm(elem(r), 35)})` : null;
          }
          if (n.op === '∘') {
            return residualSignature(COMP_SIG, [srcOf(n.l), srcOf(n.r)], {}, text, { argTypes: [await typeOf(n.l), await typeOf(n.r)] });
          }
          if (n.op === '∘ₛₗ' || n.op === '∘ₗ' || n.op === '≪≫ₗ') {
            // `g ∘ₛₗ f` is `LinearMap.comp g f`, `e ≪≫ₗ e'` is `LinearEquiv.trans e e'`.
            const fSig = await lookup(n.op === '≪≫ₗ' ? 'LinearEquiv.trans' : 'LinearMap.comp');
            if (!fSig) return null;
            const argTypes = [await typeOf(n.l), await typeOf(n.r)];
            return residualSignature(fSig, [srcOf(n.l), srcOf(n.r)], {}, text,
              { argTypes, valueTypes: await valueTypesOf(argTypes), instances: await instancesIn() });
          }
          if (n.op === '^' || n.op === '•') {
            const t = await typeOf(n.op === '•' ? n.r : n.l);
            return t && t !== 'Prop' && !isPropType(t) ? t : null;
          }
          if (!ARITH_OPS.has(n.op)) return null;
          // `2 * π * k * s`: Lean elaborates the whole tree at the widest type of its leaves (ℤ
          // coerced to ℝ). Numerals and `↑x` adapt; any other unknown leaf leaves it unknown.
          const leaves = [];
          const collect = (m) => {
            const c = m.paren ? m : m;
            if (c.k === 'bin' && ARITH_OPS.has(c.op)) { collect(c.l); collect(c.r); } else leaves.push(c);
          };
          collect(n);
          const fixed = leaves.filter(x => x.k !== 'num' && !(x.k === 'pre' && x.op === '↑'));
          if (!fixed.length) return null;
          const types = await Promise.all(fixed.map(typeOf));
          if (types.some(t => !t || t === 'Prop' || isPropType(t))) return null;
          return widestType(types);
        }
        case 'pre':
          if (n.op === '¬') return 'Prop';
          if (n.op === '√') return 'ℝ'; // `Real.sqrt`
          return n.op === '-' ? typeOf(n.e) : null;
        case 'post': case 'abs': return typeOf(n.e);
        case 'norm': return 'ℝ';
        case 'tuple': {
          // `(a, b) : A × B` (`×` is right-associative: `(a, b, c) : A × B × C`).
          if (!n.pair) return null;
          const ts = await Promise.all(n.es.map(typeOf));
          if (!ts.every(Boolean)) return null;
          return ts.map((t, k) => (/ → /.test(t) || (k < ts.length - 1 && / × /.test(t)) ? `(${t})` : t)).join(' × ');
        }
        case 'bind': {
          if (n.head === '∀' || n.head === 'Π') {
            // A pi type: a proposition when its body is one (`∀ x, p x`), else a type
            // (`∀ i, AddCommMonoid (s i) : Type (max u_1 u_8)`).
            const body = await typeOf(n.body);
            if (body === 'Prop') return 'Prop';
            if (!sortOf(parseTerm(body || ''))) return body || n.arrow || n.head === 'Π' || !isPropType(showTerm(n.body)) ? null : 'Prop';
            const bt = await binderTypeIn(n);
            const sort = bt ? piSort(await typeOf(parseTerm(bt) || { k: 'raw', v: bt }), body) : null;
            // Shown as Lean prints it: `(i : ι) → AddCommMonoid (s i)` (a type, so an arrow).
            if (sort && hint.binders && !/[:(){}]/.test(n.binders)) hint.binders.set(n, { binders: `(${n.binders.trim()} : ${bt})`, arrow: sort !== 'Prop' });
            return sort;
          }
          if (['∃', '∃!'].includes(n.head)) return 'Prop';
          if (n.head === 'fun' || n.head === 'λ') {
            // `fun (x : ℝ) (n : ℕ) => b : ℝ → ℕ → B`; untyped binders need the expected type.
            const groups = [...n.binders.matchAll(/\(\s*([^():]+?)\s*:\s*([^()]*(?:\([^()]*\)[^()]*)*)\)/g)];
            const covered = groups.map(g => g[0]).join(' ').replace(/\s+/g, '');
            if (!groups.length || covered !== n.binders.replace(/\s+/g, '')) return null;
            const body = await typeOf(n.body);
            const bodyT = body && parseTerm(body);
            if (!bodyT) return null;
            const rest = groups.flatMap(g => g[1].trim().split(/\s+/).map(name => ({ name, type: parseTerm(g[2].trim()), bi: '(' })));
            return rest.some(x => !x.type) ? null : showTerm(piOf(rest, bodyT));
          }
          return ['∑', '∏', "∑'", "∏'", '∫', '⋃', '⋂', '⨆', '⨅'].includes(n.head) ? typeOf(n.body) : null;
        }
        default: return null;
      }
    };
    // The type of a binder's (single) variable: written (`(i : ι)`, `x : T`), or from its
    // first use as an argument of a local function (`s i` with `s : ι → Type u_8`).
    const binderTypeIn = async (n) => {
      const b = n.binders.trim();
      const typed = b.match(/^[({⦃]?\s*[^\s:(){}]+(?:\s+[^\s:(){}]+)*\s*:\s*([\s\S]+?)\s*[)}⦄]?$/);
      if (typed) return typed[1];
      const names = binderParts(b).names;
      if (names.length !== 1) return null;
      const x = names[0];
      let found = null;
      const visit = (m) => {
        if (found || !m) return;
        if (m.k === 'app' && tCore(m.f).k === 'id') {
          const k = m.args.findIndex(a => tCore(a).k === 'id' && tCore(a).v === x);
          if (k !== -1) { found = { f: tCore(m.f).v, k }; return; }
        }
        tChildren(m).forEach(visit);
      };
      visit(n.body);
      if (!found || !LOCAL_NAME.test(found.f)) return null;
      const ft = await localSig(found.f);
      if (typeof ft !== 'string') return null;
      let t = tCore(parseTerm(ft));
      for (let k = 0; t && k <= found.k; k++) {
        let dom = null;
        if (t.k === 'bin' && t.op === '→') { dom = t.l; t = t.r; }
        else if (t.k === 'bind' && (t.head === 'Π' || t.head === '∀')) {
          const m = t.binders.match(/^\(\s*\S+\s*:\s*([\s\S]+)\)$/);
          dom = m ? parseTerm(m[1]) : null;
          t = t.body;
        } else return null;
        if (k === found.k) return dom ? showTerm(dom) : null;
      }
      return null;
    };
    // Types of subterms keep their ascriptions (matching sees through them); only what is
    // shown at the end is printed the way Lean prints it.
    const typeOf = async (n) => displayType(await sigOfTerm(n), text, true);
    // Instance arguments in scope (the declaration's own and the file's `variable`s), for
    // out-params instance search would find.
    let instancesP = null;
    const instancesIn = () => (instancesP = instancesP || (async () => {
      const own = [...(text.slice(0, Math.max(0, headerEnd(text))).matchAll(/\[(?:[^\[\]:]+:\s*)?([^\[\]]+)\]/g))].map(m => m[1].trim());
      let file = [];
      if (hint.instances) { try { file = (await hint.instances()) || []; } catch (err) { file = []; } }
      return [...own, ...file];
    })());
    // Types of the locals named in arguments' types (`σ₁₂`, `s` in `f : Π i, s i →ₛₗ[σ₁₂] t i`),
    // for the variables solved by them.
    const valueTypes = new Map();
    const valueTypeLookups = new Map(); // name → pending lookup
    const valueTypesOf = async (argTypes) => {
      const names = new Set();
      for (const t of argTypes) {
        (typeof t === 'string' ? t : '').replace(/(?<![\w'.])[^\s()[\]{}⟨⟩,:.→↦∀∃=<>≤≥+*•∘|]+/g, (m) => {
          if (Object.prototype.hasOwnProperty.call(TYPE_SORTS, m)) valueTypes.set(m, TYPE_SORTS[m]); // `ℝ : Type`
          else if (LOCAL_NAME.test(m)) names.add(m);
          return m;
        });
      }
      // Looked up in parallel (each may be a message to the worker), once per name: concurrent
      // callers share the pending lookup.
      for (const nm of [...names].slice(0, 8)) {
        if (!valueTypeLookups.has(nm)) {
          valueTypeLookups.set(nm, localSig(nm).then(t => { valueTypes.set(nm, typeof t === 'string' && !isSignature(t) ? t : null); }));
        }
      }
      await Promise.all([...names].slice(0, 8).map(nm => valueTypeLookups.get(nm)));
      return valueTypes;
    };
    // Positional / named arguments of an application and the types used to solve variables.
    const argsOf = async (n) => {
      const positional = [];
      const named = Object.create(null);
      const argNodes = [];
      for (const a of n.args) {
        if (a.k === 'named') named[a.name] = srcOf(a.value);
        else { positional.push(srcOf(a)); argNodes.push(a); }
      }
      const argTypes = await Promise.all(argNodes.map(async (a) => {
        if (a.k === 'tuple') return { tuple: await Promise.all(a.es.map(e => (['num', 'raw', 'tuple'].includes(e.k) ? null : typeOf(e)))) };
        return ['num', 'raw'].includes(a.k) ? null : typeOf(a);
      }));
      return { positional, named, argTypes };
    };

    // `have h : T := term`: variables the term leaves open are fixed by matching T, as Lean
    // elaborates the term against it (`?f ?a` against `f b` once `f` is known: matched twice).
    const solvedByExpected = (sig, expected) => {
      const r = residualParts(sig, [], {}, text);
      const tgt = parseTerm(expected);
      if (!r || !r.lead.length || !tgt) return null;
      const vars = new Set(r.lead.map(x => x.name));
      const pat = piOf(r.rest, r.concl);
      const sub = new Map();
      if (!matchTerm(pat, tgt, vars, sub)) {
        const again = new Map();
        if (!matchTerm(substTerm(pat, sub), tgt, new Set([...vars].filter(v => !sub.has(v))), again)) return null;
        again.forEach((v, k) => sub.set(k, v));
      }
      const mv = new Map(r.lead.map(x => [x.name, sub.get(x.name) || { k: 'id', v: `?${x.name}` }]));
      return showTerm(stripAscriptions(substTerm(pat, mv), text));
    };

    // Variables a term's type leaves open can be fixed by where it's used, as Lean's elaboration
    // fixes them: in `(abs_le).mpr ⟨h₁, h₂⟩` the arguments of `.mpr` fix `abs_le`'s `a` and `b`.
    const solvedByUse = async (n, sig) => {
      const path = hint.path || [];
      const parent = path[1];
      const r = sig && residualParts(sig, [], {}, text);
      if (!r || !r.lead.length || !parent) return null;
      let combined = null;
      let app = null;
      if (parent.k === 'proj' && parent.e === n) {
        combined = await fieldSig(sig, srcOf(n), parent.f);
        app = path[2] && path[2].k === 'app' && path[2].f === parent ? path[2] : null;
      } else if (parent.k === 'app' && parent.f === n) {
        combined = sig;
        app = parent;
      }
      if (!combined || !app) return null;
      const { positional, named, argTypes } = await argsOf(app);
      const inst = instantiateSignature(combined, positional, named, text, { argTypes });
      let solved = 0;
      const mv = new Map(r.lead.map((x) => {
        const v = inst.sub.get(inst.fresh(x.name));
        if (v && ![...freeNames(v)].some(y => y.startsWith('__pv_'))) { solved++; return [x.name, v]; }
        return [x.name, { k: 'id', v: `?${x.name}` }];
      }));
      return solved ? showTerm(stripAscriptions(substTerm(piOf(r.rest, r.concl), mv), text)) : null;
    };

    if (node && node.k === 'num') {
      // A numeral takes its type from where it is: `x + 1`, `0 < x`, `x ^ 2` (a natural exponent).
      const p = hint.parent;
      if (p && p.k === 'asc') return displayType(showTerm(p.ty));
      if (!p || p.k !== 'bin') return null;
      if (p.op === '^') return p.r === node ? 'ℕ' : null;
      if (!NUMERAL_SIBLING_OPS.has(p.op)) return null;
      const other = p.l === node ? p.r : p.l;
      const t = other.k === 'num' ? null : await typeOf(other);
      return t && t !== 'Prop' && !isPropType(t) ? t : null;
    }
    const sig = await sigOfTerm(node);
    const shown = (await solvedByUse(node, sig)) || displayType(sig, text);
    const out = (shown && shown.includes('?') && hint.expected && solvedByExpected(sig, hint.expected)) || shown;
    // Binders as Lean prints them, with the types of the locals around (`(i : ι) → s i`).
    return out ? annotateTextAsync(out, async (n) => { const t = await localSig(n); return typeof t === 'string' ? t : null; }) : out;
  }

  /**
   * `annotateText` with an asynchronous `typeOfName`: the names used in the text (and in
   * their types) are looked up first.
   */
  async function annotateTextAsync(text, typeOfName) {
    if (!/[∀Π⨂⨁]|\b(?:fun|λ)\b/.test(text || '')) return text;
    const types = new Map();
    let pending = new Set((text.match(/(?<![\w'.])[A-Za-z_\u0370-\u03FF\u1F00-\u1FFF][\w'\u0370-\u03FF\u1F00-\u1FFF\u2080-\u209C]*/g) || []));
    for (let round = 0; round < 2 && pending.size; round++) {
      const next = new Set();
      const batch = [...pending].slice(0, 16).filter(n => !types.has(n) && !USE_NOT_FN.has(n));
      batch.forEach(n => types.set(n, null));
      await Promise.all(batch.map(async (n) => {
        let t = null;
        try { t = await typeOfName(n); } catch (err) { t = null; }
        types.set(n, t);
        if (t) (t.match(/(?<![\w'.])[A-Za-z_\u0370-\u03FF][\w'\u0370-\u03FF\u2080-\u209C]*/g) || []).forEach(x => { if (!types.has(x)) next.add(x); });
      }));
      pending = next;
    }
    return annotateText(text, (n) => types.get(n) || null);
  }

  Object.assign(scope.VersoBinderContext, {
    annotateTextAsync, termAtOffset, termTypeOf, termDisplay, notationDocName, joinStatement,
    statementAround
  });
})();
