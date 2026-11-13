/**
 * Lean terms as Lean Lens models them, without Lean: a parser and printer for the term
 * syntax that shows up in hovers (applications, operators, binders, bundled-map arrows,
 * semilinear notation, universes), matching with variables (unification, also higher-order
 * patterns), signatures (instantiating a constant at its arguments, residual types), and
 * printing types the way Lean's hover does. Pure functions of strings and syntax trees.
 *
 * Used by binder_context.js (locals, rewrite replay), term_hover.js (gap hovers),
 * pr_scanner.js and the service worker, through the global `LeanTerms`.
 */

(function () {
  // Supplied by binder_context.js: a local's written type in a declaration's text.
  const hooks = { localType: () => null };
  const localType = (name, text) => hooks.localType(name, text);

  const OPENERS = { '(': ')', '{': '}', '⦃': '⦄', '[': ']', '⟨': '⟩' };
  Object.setPrototypeOf(OPENERS, null); // looked up by words from the source: no `constructor`, `toString`, … from Object

  const CLOSERS = new Set(Object.values(OPENERS));

  // Bundled-map notations (checked against Mathlib via Loogle patterns).
  // Bracket arguments are normalised to `[_]` / `⁅_⁆` before lookup.
  const ARROW_HEADS = {
    '→': null, '->': null,
    '→ₘₗ[_]': 'MultilinearMap', '→ₘₛₗ[_]': 'MultilinearMap',
    '→ₗ[_]': 'LinearMap', '→ₛₗ[_]': 'LinearMap',
    '≃ₗ[_]': 'LinearEquiv', '≃ₛₗ[_]': 'LinearEquiv',
    '→L[_]': 'ContinuousLinearMap', '→SL[_]': 'ContinuousLinearMap',
    '≃L[_]': 'ContinuousLinearEquiv', '≃SL[_]': 'ContinuousLinearEquiv',
    '→ₗ.[_]': 'LinearPMap',
    '→+': 'AddMonoidHom', '→*': 'MonoidHom', '→+*': 'RingHom', '→*₀': 'MonoidWithZeroHom',
    '→ₙ+': 'AddHom', '→ₙ*': 'MulHom', '→ₙ+*': 'NonUnitalRingHom',
    '≃+': 'AddEquiv', '≃*': 'MulEquiv', '≃+*': 'RingEquiv',
    '→ₐ[_]': 'AlgHom', '≃ₐ[_]': 'AlgEquiv', '→ₙₐ[_]': 'NonUnitalAlgHom',
    '→⋆ₐ[_]': 'StarAlgHom', '≃⋆ₐ[_]': 'StarAlgEquiv',
    '→ₗ⁅_⁆': 'LieHom', '≃ₗ⁅_⁆': 'LieEquiv',
    '→+[_]': 'DistribMulActionHom', '→[_]': 'MulActionHom', '→ₑ[_]': 'MulActionHom',
    '≃': 'Equiv', '↪': 'Function.Embedding',
    '→o': 'OrderHom', '≃o': 'OrderIso', '↪o': 'OrderEmbedding',
    '→r': 'RelHom', '≃r': 'RelIso', '↪r': 'RelEmbedding',
    '→ᵃ[_]': 'AffineMap', '≃ᵃ[_]': 'AffineEquiv', '→ᴬ[_]': 'ContinuousAffineMap',
    '→ₗᵢ[_]': 'LinearIsometry', '≃ₗᵢ[_]': 'LinearIsometryEquiv',
    '≃ᵢ': 'IsometryEquiv', '≃ₜ': 'Homeomorph', '≃ᵐ': 'MeasurableEquiv',
    '→ᵇ': 'BoundedContinuousFunction', '→₀': 'Finsupp',
    '→ₘ[_]': 'MeasureTheory.AEEqFun', '→ₛ': 'MeasureTheory.SimpleFunc',
    '→ₚ[_]': 'PositiveLinearMap', '→A[_]': 'ContinuousAlgHom', '→ₗc[_]': 'CoalgHom',
    '→*o': 'OrderMonoidHom', '→+o': 'OrderAddMonoidHom', '→*₀o': 'OrderMonoidWithZeroHom',
    '≃*o': 'OrderMonoidIso', '→+*o': 'OrderRingHom', '≃+*o': 'OrderRingIso', '≃⋆+*': 'StarRingEquiv'
  };
  Object.setPrototypeOf(ARROW_HEADS, null);

  // Prefix notations: `C(α, β)` etc.
  const PREFIX_HEADS = [
    ['C₀(', 'ZeroAtInftyContinuousMap'],
    ['C_c(', 'CompactlySupportedContinuousMap'],
    ['C(', 'ContinuousMap'],
    ['𝓢(', 'SchwartzMap']
  ];

  // Lowest precedence first: the first one found at depth 0 is the head.
  // (Arrow-like notations are handled separately, between `↔` and the rest.)
  const INFIX_HEADS = [
    ['∨', 'Or'],
    ['∧', 'And'],
    ['≠', 'Ne'],
    ['≤', 'LE.le'],
    ['≥', 'GE.ge'],
    ['⊆', 'HasSubset.Subset'],
    ['⊂', 'HasSSubset.SSubset'],
    ['∉', null],
    ['∈', 'Membership.mem'],
    ['∣', 'Dvd.dvd'],
    ['=', 'Eq'],
    ['<', 'LT.lt'],
    ['>', 'GT.gt']
  ];

  const NOTATION_HEADS = {
    'ℕ': 'Nat', 'ℤ': 'Int', 'ℚ': 'Rat', 'ℝ': 'Real', 'ℂ': 'Complex',
    'Prop': null, 'Type': null, 'Sort': null
  };
  Object.setPrototypeOf(NOTATION_HEADS, null);

  /** Index of the closer matching the opener at `openIdx`, or -1. */
  function matchClose(text, openIdx) {
    const stack = [OPENERS[text[openIdx]]];
    for (let i = openIdx + 1; i < text.length; i++) {
      const ch = text[i];
      if (OPENERS[ch]) stack.push(OPENERS[ch]);
      else if (CLOSERS.has(ch)) {
        if (ch !== stack[stack.length - 1]) return -1;
        stack.pop();
        if (stack.length === 0) return i;
      }
    }
    return -1;
  }

  /** Position of `op` at bracket depth 0, or -1. */
  function topLevelIndexOf(text, op) {
    let depth = 0;
    for (let i = 0; i < text.length; i++) {
      const ch = text[i];
      if (OPENERS[ch]) depth++;
      else if (CLOSERS.has(ch)) depth = Math.max(0, depth - 1);
      else if (depth === 0 && text.startsWith(op, i)) {
        // `->` must not be mistaken for `>`, `≥`/`≤` already distinct characters.
        if (op === '>' && (text[i - 1] === '-' || text[i - 1] === '=')) continue;
        if (op === '<' && (text[i + 1] === '|' || text[i + 1] === ';')) continue;
        if (op === '=' && (text[i - 1] === ':' || text[i + 1] === '>')) continue;
        return i;
      }
    }
    return -1;
  }

  /**
   * Leftmost top-level arrow-like operator (`→`, `→ₗ[R]`, `≃+*`, `↪o`, …), normalised
   * so bracket arguments read `[_]`; null if none. `→` is right-associative, so the
   * leftmost one is the head.
   */
  function topLevelArrow(text) {
    let depth = 0;
    for (let i = 0; i < text.length; i++) {
      const ch = text[i];
      if (OPENERS[ch]) { depth++; continue; }
      if (CLOSERS.has(ch)) { depth = Math.max(0, depth - 1); continue; }
      if (depth !== 0) continue;
      const isArrow = ch === '→' || ch === '≃' || ch === '↪' || (ch === '-' && text[i + 1] === '>');
      if (!isArrow || i === 0) continue;
      let j = i + (ch === '-' ? 2 : 1);
      let op = text.slice(i, j);
      while (j < text.length && !/\s/.test(text[j])) {
        if (text[j] === '[' || text[j] === '⁅') {
          const close = text.indexOf(text[j] === '[' ? ']' : '⁆', j);
          if (close === -1) break;
          op += text[j] === '[' ? '[_]' : '⁅_⁆';
          j = close + 1;
        } else if (text[j] === '(') {
          break;
        } else {
          op += text[j++];
        }
      }
      return op;
    }
    return null;
  }

  /**
   * Codomain of a (bundled) function type: the text after its leftmost top-level arrow-like
   * operator (`Rˣ →* R ≃o R` → `R ≃o R`). Applying a bundled map coerces it to a function.
   */
  function codomainOf(type) {
    if (!type) return null;
    const t = type.replace(/\s+/g, ' ').trim();
    let depth = 0;
    for (let i = 1; i < t.length; i++) {
      const ch = t[i];
      if (OPENERS[ch]) depth++;
      else if (CLOSERS.has(ch)) depth = Math.max(0, depth - 1);
      else if (depth === 0 && (ch === '→' || ch === '≃' || ch === '↪')) {
        const sp = t.indexOf(' ', i);
        return sp === -1 ? null : t.slice(sp + 1).trim();
      }
    }
    return null;
  }

  /**
   * Head constant of a type expression, as a namespace for field notation.
   * `resolveVar(v)` gives the head of a local variable's type (or null).
   */
  function typeHead(type, resolveVar) {
    if (!type) return null;
    let t = type.replace(/\s+/g, ' ').trim()
      // Notation for types: `ℝ≥0∞` is ENNReal (not the infix `≥`), `ℝ≥0` NNReal, …
      .replace(/ℝ≥0∞/g, 'ENNReal').replace(/ℝ≥0/g, 'NNReal').replace(/ℚ≥0/g, 'NNRat').replace(/ℕ∞/g, 'ENat');

    // Strip redundant outer parentheses.
    while (t.startsWith('(') && matchClose(t, 0) === t.length - 1) t = t.slice(1, -1).trim();

    if (/^(∀|Π|fun\b|λ)/.test(t)) return null;
    if (t.startsWith('∃!')) return 'ExistsUnique';
    if (t.startsWith('∃')) return 'Exists';
    if (t.startsWith('¬')) return 'Not';

    // A lambda / binder at top level runs to the end: operators after it belong to its body.
    // (Only at depth 0: `(∀ᶠ x in l, ∀ i ∈ I, p i x) ↔ …` is still an `↔`.)
    let cut = -1;
    for (let i = 0, depth = 0; i < t.length && cut === -1; i++) {
      const ch = t[i];
      if (OPENERS[ch]) depth++;
      else if (CLOSERS.has(ch)) depth = Math.max(0, depth - 1);
      else if (depth === 0 && i > 0 && /^(\s(fun\b|λ|∀|∃|Π)|=>|↦)/.test(t.slice(i, i + 5))) cut = i;
    }
    const head = cut > 0 ? t.slice(0, cut) : t;
    if (topLevelIndexOf(head, '↔') > 0) return 'Iff';
    const arrow = topLevelArrow(head);
    if (arrow !== null) {
      // Unknown decorated arrow: some bundled map we don't know; don't guess.
      return Object.prototype.hasOwnProperty.call(ARROW_HEADS, arrow) ? ARROW_HEADS[arrow] : null;
    }

    for (const [prefix, head] of PREFIX_HEADS) {
      if (t.startsWith(prefix)) return head;
    }

    for (const [op, h] of INFIX_HEADS) {
      if (topLevelIndexOf(head, op) > 0) return h;
    }
    // `R⟦X⟧` is a power series ring, `R[X]` a polynomial ring.
    if (/⟦X⟧$/.test(t)) return 'PowerSeries';
    if (/\[X\]$/.test(t) && !/\s/.test(t.replace(/^\(.*\)/, ''))) return 'Polynomial';
    // `(term).Field`: generalized field notation on a term we can't type; the field's
    // name is a partial namespace (`((cantorNF b o).map Prod.fst).SortedGT` → `SortedGT`).
    // `{p : ℕ | p.Prime}.Finite` is `Set.Finite {p : ℕ | p.Prime}`.
    if (t.startsWith('{')) {
      const close = matchClose(t, 0);
      const after = close > 0 ? t.slice(close + 1).match(/^\.([A-Za-z][\w'\u2080-\u2089]*)$/) : null;
      if (after && t.slice(1, close).includes('|')) return `Set.${after[1]}`;
    }
    if (t.startsWith('(')) {
      const close = matchClose(t, 0);
      const after = close > 0 ? t.slice(close + 1).match(/^\.([A-Z][\w'\u2080-\u2089]*)/) : null;
      if (after) {
        // `(s : Set ℕ).Finite`: in the ascribed type's namespace.
        const inner = t.slice(1, close);
        const c = topColon(inner);
        const ns = c !== -1 ? typeHead(inner.slice(c + 1), resolveVar) : null;
        return ns ? `${ns}.${after[1]}` : after[1];
      }
    }

    const m = t.match(/^@?([^\s()\[\]{}⟨⟩,]+)/);
    if (!m) return null;
    const ident = m[1].replace(/\.+$/, '');
    if (Object.prototype.hasOwnProperty.call(NOTATION_HEADS, ident)) return NOTATION_HEADS[ident];

    const segs = ident.split('.');
    const startsLower = /^[a-z_α-ωϑ-ϻ]/.test(segs[0]);

    if (startsLower && segs.length > 1) {
      // Generalized field notation in the type itself: `l.SortedLT` = `List.SortedLT l`.
      const rest = segs.slice(1);
      if (rest.length === 1 && resolveVar) {
        const varHead = resolveVar(segs[0]);
        if (varHead) return `${varHead}.${rest[0]}`;
      }
      return rest[rest.length - 1];
    }
    if (startsLower) return null; // a variable or bound name, not a constant
    return ident;
  }

  /**
   * The conclusion of a type: drop a Loogle-style `binders :` prefix, leading `∀ …,`
   * binders and `→` premises. `(h : ContinuousAt f x) : Filter.Tendsto f …` → `Filter.Tendsto f …`;
   * `∀ s : ℝ, |s| < b → C ≤ c` → `C ≤ c`.
   */
  function conclusionOf(type) {
    if (!type) return null;
    let t = type.replace(/\s+/g, ' ').trim();
    if (/^:(?!=)/.test(t)) t = t.slice(1).trim(); // a signature with no parameters: `: T`
    // Loogle signatures: leading binder groups, then ` : conclusion`.
    let i = 0;
    while (i < t.length && OPENERS[t[i]] && t[i] !== '⟨') {
      const close = matchClose(t, i);
      if (close === -1) break;
      i = close + 1;
      while (t[i] === ' ') i++;
    }
    if (i > 0 && t[i] === ':' && t[i + 1] !== '=') t = t.slice(i + 1).trim();
    for (let guard = 0; guard < 20; guard++) {
      while (t.startsWith('(') && matchClose(t, 0) === t.length - 1) t = t.slice(1, -1).trim();
      if (/^(∀|Π)/.test(t)) {
        const comma = topLevelIndexOf(t, ',');
        if (comma === -1) return null;
        t = t.slice(comma + 1).trim();
        continue;
      }
      // Last top-level plain arrow (not a bundled-map notation like `→ₗ[R]`).
      let depth = 0;
      let cut = -1;
      for (let k = 0; k < t.length; k++) {
        const ch = t[k];
        if (OPENERS[ch]) depth++;
        else if (CLOSERS.has(ch)) depth = Math.max(0, depth - 1);
        else if (depth === 0 && ch === '→' && (t[k + 1] === ' ' || k + 1 === t.length)) cut = k;
      }
      if (cut !== -1) { t = t.slice(cut + 1).trim(); continue; }
      break;
    }
    return t || null;
  }

  /** Leading identifier of an application `f a b`, e.g. `ContinuousAt.tendsto (h := …)` → `ContinuousAt.tendsto`. */
  function applicationHead(expr) {
    const m = (expr || '').match(/^@?([A-Za-z_\u0370-\u03FF][\w'.\u0370-\u03FF\u2080-\u2089!?]*)/);
    return m ? m[1].replace(/\.+$/, '') : null;
  }

  const IDENT_SPLIT = /[^A-Za-z0-9_'!?\u2080-\u2089\u0370-\u03FF\u1F00-\u1FFF]+/;

  const namesIn = (s) => s.split(IDENT_SPLIT).filter(Boolean);

  /** Index of the first `:` at bracket depth 0 (not `:=`), or -1. */
  function topColon(s) {
    let depth = 0;
    for (let k = 0; k < s.length; k++) {
      const ch = s[k];
      if (OPENERS[ch]) depth++;
      else if (CLOSERS.has(ch)) depth = Math.max(0, depth - 1);
      else if (ch === ':' && depth === 0 && s[k + 1] !== '=') return k;
    }
    return -1;
  }

  const stripParens = (x) => {
    x = (x || '').replace(/\s+/g, ' ').trim();
    while (x.startsWith('(') && matchClose(x, 0) === x.length - 1) x = x.slice(1, -1).trim();
    return x;
  };

  /**
   * Replace the identifier `word` (not part of a longer name or a field access `x.word`;
   * after a range `a..word` it counts as a name).
   */
  function replaceWord(text, word, value) {
    const esc = word.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    return text.replace(new RegExp(`(?<![\\w'\\u2080-\\u209C])(?<!(?:^|[^.])\\.)${esc}(?![\\w'\\u2080-\\u209C])`, 'g'), () => value);
  }

  /** Split at depth-0 occurrences of `sep`. */
  function splitTop(text, sep) {
    const parts = [];
    let depth = 0;
    let last = 0;
    for (let i = 0; i < text.length; i++) {
      const ch = text[i];
      if (OPENERS[ch]) depth++;
      else if (CLOSERS.has(ch)) depth = Math.max(0, depth - 1);
      else if (depth === 0 && text.startsWith(sep, i)) {
        parts.push(text.slice(last, i));
        last = i + sep.length;
        i += sep.length - 1;
      }
    }
    parts.push(text.slice(last));
    return parts.map(p => p.trim());
  }

  const USE_NOT_FN = new Set(['fun', 'λ', 'Π', 'Σ', 'by', 'at', 'with', 'from', 'using', 'then', 'else', 'in', 'do', 'have', 'show', 'let', 'if', 'match', 'Type', 'Sort']);

  /** The first `f a₁ … name` after `from`: { fn, k } (name is f's k-th explicit argument), or null. */
  // One regular expression per name (they're built a lot while printing signatures).
  const useRegex = memoized((name) => {
    const esc = name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    return new RegExp(`(?<![\\w'.\\u0370-\\u03FF\\u2080-\\u209C])([A-Za-z_\\u0370-\\u03FF\\u1F00-\\u1FFF][\\w'.\\u0370-\\u03FF\\u1F00-\\u1FFF\\u2080-\\u209C]*)((?:[ \\t]+(?:[\\w'\\u0370-\\u03FF\\u2080-\\u209C]+|\\([^()\\n]*\\)))*?)[ \\t]+${esc}(?![\\w'\\u2080-\\u209C]|\\.[A-Za-z_\\u0370-\\u03FF])`, 'g'); // not `x.field`
  }, 500);

  function useOf(name, text, from = 0) {
    const re = useRegex(name);
    re.lastIndex = from;
    let m;
    while ((m = re.exec(text)) !== null) {
      if (USE_NOT_FN.has(m[1]) || m[1] === name) { re.lastIndex = m.index + 1; continue; }
      const args = (m[2].match(/[\w'\u0370-\u03FF\u2080-\u209C]+|\([^()\n]*\)/g) || []);
      if (args.some(a => USE_NOT_FN.has(a))) { re.lastIndex = m.index + 1; continue; }
      return { fn: m[1], k: args.length };
    }
    return null;
  }

  /**
   * The type of the k-th explicit argument of a function of type `fnType` (see
   * `domainSync`), with an asynchronous `typeOfName`: the names it asks for are looked up
   * first (in parallel), then it is worked out again. Promise of text or null.
   */
  async function domainOf(fnType, k, typeOfName) {
    const types = new Map();
    for (let round = 0; round < 4; round++) {
      const missing = new Set();
      const result = domainSync(fnType, k, (n) => { if (types.has(n)) return types.get(n); missing.add(n); return null; });
      if (!missing.size) return result;
      await Promise.all([...missing].map(async (n) => {
        let t = null;
        try { t = await typeOfName(n); } catch (err) { t = null; }
        types.set(n, t);
      }));
    }
    return domainSync(fnType, k, (n) => types.get(n) || null);
  }


  /**
   * The type of the k-th explicit argument of a function of type `fnType`: `A → B`,
   * `(x : A) → B`, `∀ (x : A), B`, a bundled map `A →ₗ[R] B` (its points); an untyped
   * `Π i, …` binder is found from its own use (`s i`) through `typeOfName`. Text or null.
   */
  function domainSync(fnType, k, typeOfName, depth = 0) {
    let t = tCore(parseTerm(fnType || ''));
    for (let j = 0; t && j <= k; j++) {
      let dom = null;
      if (t.k === 'bin' && (t.op === '→' || isBundledType(t))) { dom = t.l; t = t.op === '→' ? t.r : null; }
      else if (t.k === 'bind' && (t.head === 'Π' || t.head === '∀')) {
        const typed = t.binders.match(/^[({⦃]?\s*[^\s:(){}]+\s*:\s*([\s\S]+?)\s*[)}⦄]?$/);
        if (typed) dom = parseTerm(typed[1]);
        else if (depth < 2 && binderParts(t.binders).names.length === 1) {
          const use = useOf(binderParts(t.binders).names[0], showTerm(t.body));
          const ft = use && typeOfName(use.fn);
          const d = ft ? domainSync(ft, use.k, typeOfName, depth + 1) : null;
          dom = d ? parseTerm(d) : null;
        }
        t = t.body;
      } else return null;
      if (j === k) return dom ? showTerm(annotateBinders(dom, typeOfName)) : null;
      if (!t) return null;
    }
    return null;
  }

  // Classes whose instances are proofs: `[∀ i, Nonempty (α i)]` stays a `∀`.
  const PROP_CLASSES = new Set(['Nonempty', 'IsEmpty', 'Fact', 'Subsingleton', 'Nontrivial', 'Finite', 'Infinite', 'Countable',
    'Uncountable', 'IsScalarTower', 'SMulCommClass', 'IsCentralScalar', 'IsDomain', 'CharZero', 'CharP', 'NoZeroDivisors',
    'NoZeroSMulDivisors', 'FiniteDimensional', 'IsNoetherian', 'IsArtinian', 'Free', 'Flat', 'Projective', 'T0Space', 'T1Space',
    'T2Space', 'T3Space', 'RegularSpace', 'NormalSpace', 'CompactSpace', 'LocallyCompactSpace', 'SecondCountableTopology',
    'FirstCountableTopology', 'SeparableSpace', 'CompleteSpace', 'ProperSpace', 'IsTopologicalGroup', 'IsTopologicalRing',
    'IsTopologicalAddGroup', 'ContinuousSMul', 'ContinuousAdd', 'ContinuousMul', 'BorelSpace', 'OpensMeasurableSpace',
    'MeasurableSingletonClass', 'IsFiniteMeasure', 'IsProbabilityMeasure', 'SigmaFinite', 'IsOrderedRing', 'IsStrictOrderedRing',
    'IsOrderedAddMonoid', 'IsOrderedCancelAddMonoid', 'IsLocalRing', 'IsPrincipalIdealRing', 'IsDedekindDomain', 'IsIntegrallyClosed']);

  /**
   * Binders as Lean prints them, their types worked out from their use (`typeOfName` gives the
   * types of the names around): `Π i, s i` is `(i : ι) → s i`, `⨂[R] i, s i` is
   * `⨂[R] (i : ι), s i`, `∀ f, P f` is `∀ (f : T), P f`. `instance`: `n` is an instance
   * argument's type (a class, so data unless a `Prop` class: `[(i : ι) → AddCommMonoid (s i)]`).
   */
  function annotateBinders(n, typeOfName, instance = false) {
    if (!n || typeof n !== 'object') return n;
    const m = tWithChildren(n, tChildren(n).map(c => annotateBinders(c, typeOfName)));
    if (m.k !== 'bind' || m.arrow || !['∀', 'Π', '⨂[_]', '⨂ₜ[_]', '⨁'].includes(m.head)) return m;
    const b = m.binders.trim();
    // `⨂[R] i : ι, s i` / `∀ x : T, P`: Lean prints the binder in parentheses.
    // (Its type may have binders of its own: `f : Π i, s i`.)
    const typedBare = b.match(/^([^\s:(){}⦃⦄[\]]+(?:\s+[^\s:(){}⦃⦄[\]]+)*)\s*:\s*([\s\S]+)$/);
    if (typedBare && (!typedBare[2].includes(',') || innerCommas(b) === 0) && !binderParts(b).op) {
      const binders = `(${typedBare[1]} : ${annotateText(typedBare[2].trim(), typeOfName)})`;
      if ((m.head === 'Π') || (m.head === '∀' && isDataType(m.body))) return { k: 'bind', head: 'Π', arrow: true, binders, sep: '→', body: m.body };
      return Object.assign({}, m, { binders });
    }
    if (!b || /[:(){}⦃⦄[\]]/.test(b) || binderParts(b).op) return m;
    const names = b.split(/\s+/);
    const body = showTerm(m.body);
    const types = names.map(x => {
      const use = useOf(x, body);
      const ft = use && typeOfName(use.fn);
      return (ft ? argDomain(ft, use.k, typeOfName) : null) || operandType(x, m.body, typeOfName);
    });
    if (types.some(t => !t) || types.some(t => t !== types[0])) return m;
    const binders = `(${names.join(' ')} : ${types[0]})`;
    if (m.head === '∀' || m.head === 'Π') {
      const cls = tCore(m.body) && (tCore(m.body).k === 'app' ? tCore(tCore(m.body).f) : tCore(m.body));
      const data = m.head === 'Π' || isDataType(m.body) ||
        (instance && cls && cls.k === 'id' && !PROP_CLASSES.has(cls.v.split('.').pop()));
      return data ? { k: 'bind', head: 'Π', arrow: true, binders, sep: '→', body: m.body } : Object.assign({}, m, { binders });
    }
    return Object.assign({}, m, { binders });
  }

  /**
   * The type of the k-th explicit argument of a function whose type or signature is `ft`
   * (`IsRight (l : Link R T) (i : ι) : Prop`, argument 1: `ι`). A binder type that mentions the
   * signature's other binders is kept only when the names around have those types too (the
   * section variables a PR's declarations share), since it is the callee's own otherwise.
   */
  function argDomain(ft, k, typeOfName) {
    // (A constant without parameters: `: ℕ → ℕ`, its type.)
    if (/^\s*:(?!=)/.test(ft)) ft = ft.trim().slice(1).trim();
    if (!isSignature(ft)) return domainSync(ft, k, typeOfName);
    const p = peelSignature(ft);
    const explicit = p.binders.filter(b => b.explicit).flatMap(b => b.names.map(() => b.type));
    if (k >= explicit.length) return null;
    const type = explicit[k];
    const used = freeNames(parseTerm(type) || { k: 'raw', v: type });
    const norm = (t) => (t || '').replace(/\s+/g, ' ').trim();
    for (const b of p.binders) {
      for (const n of b.names) {
        if (used.has(n) && norm(typeOfName(n)) !== norm(b.type)) return null;
      }
    }
    return type;
  }

  // Operations whose two sides have one type: `lo < y` gives `y` the type of `lo`.
  const SAME_SIDES = new Set(['<', '≤', '>', '≥', '=', '≠', '+', '-', '*', '/', '⊆', '⊂', '⊇', '⊃', '∣', '⊔', '⊓', '∪', '∩', '\\']);

  /**
   * The type of the bound name `x` from a name on the other side of an operation with it
   * (`∀ y, lo < y → …` with `lo : ℝ`), as Lean's unification finds it; null if none is known.
   */
  function operandType(x, n, typeOfName) {
    let found = null;
    const visit = (t) => {
      if (found || !t || typeof t !== 'object') return;
      if (t.k === 'bind' && binderParts(t.binders).names.includes(x)) return; // `x` rebound
      if (t.k === 'bin' && SAME_SIDES.has(t.op)) {
        const l = tCore(t.l), r = tCore(t.r);
        const other = l && l.k === 'id' && l.v === x ? r : (r && r.k === 'id' && r.v === x ? l : null);
        const ty = other && other.k === 'id' && other.v !== x ? typeOfName(other.v) : null;
        // (A type, not a constant's signature `(n : ℕ) : ℝ`.)
        if (ty && !/^[:({[⦃]/.test(ty.trim()) && topColon(ty) === -1) { found = ty.trim(); return; }
      }
      tChildren(t).forEach(visit);
    };
    visit(n);
    return found;
  }

  /** `annotateBinders` on a type's text (unchanged when it doesn't parse). */
  function annotateText(text, typeOfName, instance = false) {
    return annotateTextNow(text, typeOfName, instance);
  }

  function annotateTextNow(text, typeOfName, instance = false) {
    const n = parseTerm(text || '');
    return n ? showTerm(noDotNames(elabAscriptions(plainFunBinders(coerceApps(annotateBinders(n, typeOfName, instance), typeOfName)), typeOfName), typeOfName)) : text;
  }

  /** The type of a name, or of a pair of names, the signature gives (for ascriptions); else null. */
  function knownTypeOf(e, typeOfName) {
    if (e.k === 'id' && LOCAL_NAME.test(e.v)) {
      const t = typeOfName(e.v);
      return t && !/^[:({[⦃]/.test(t.trim()) && topColon(t) === -1 ? t.trim() : null;
    }
    if (e.k === 'tuple' && e.pair) {
      const ts = e.es.map(x => knownTypeOf(x, typeOfName));
      return ts.every(Boolean) ? ts.map((t, k) => (/ → /.test(t) || (k < ts.length - 1 && / × /.test(t)) ? `(${t})` : t)).join(' × ') : null;
    }
    return null;
  }

  /**
   * Type ascriptions as Lean prints the elaborated term: none when the term has that type
   * (`((x, y) : ℝ × ℝ)` with `x y : ℝ` is `(x, y)`), a coercion when it has another (`(n : ℝ)`
   * with `n : ℕ` is `↑n`); kept when its type isn't known (a numeral's depends on the context).
   */
  function elabAscriptions(n, typeOfName) {
    if (!n || typeof n !== 'object' || !typeOfName) return n;
    const m = tWithChildren(n, tChildren(n).map(c => elabAscriptions(c, typeOfName)));
    if (m.k !== 'asc') return m;
    const own = knownTypeOf(m.e, typeOfName);
    const ownT = own && parseTerm(own);
    if (!ownT) return m;
    return sameTerm(ownT, m.ty) ? m.e : { k: 'pre', op: '↑', e: m.e };
  }

  // Declarations Lean prints without field notation (Mathlib's `@[pp_nodot]`): `p.Prime` with
  // `p : ℕ` is `Nat.Prime p`, `x.log` with `x : ℝ` is `Real.log x`.
  const PP_NODOT = new Set(['Complex.Gamma', 'Complex.besselJ', 'Complex.cos', 'Complex.cosh', 'Complex.cot', 'Complex.log',
    'Complex.normSq', 'Complex.sin', 'Complex.sinh', 'Complex.tan', 'Complex.tanh', 'DirichletCharacter.LFunction',
    'DirichletCharacter.completedLFunction', 'Int.fib', 'Int.sqrt', 'Matrix.fromBlocks', 'MinTropical.untrop', 'MulOpposite.unop',
    'NNReal.sqrt', 'Nat.Prime', 'Nat.clog', 'Nat.fib', 'Nat.log', 'Nat.pair', 'Nat.unpair', 'Ordinal.CNF', 'Ordinal.log',
    'Ordinal.veblen', 'Ordinal.veblenWith', 'Rat.nnabs', 'Rat.sqrt', 'Real.Gamma', 'Real.arccos', 'Real.arcosh', 'Real.arcsin',
    'Real.arctan', 'Real.arsinh', 'Real.artanh', 'Real.binEntropy', 'Real.cos', 'Real.cosh', 'Real.cot', 'Real.exp', 'Real.log',
    'Real.logb', 'Real.nnabs', 'Real.qaryEntropy', 'Real.sin', 'Real.sinc', 'Real.sinh', 'Real.tan', 'Real.tanh', 'SymAlg.unsym']);

  /** `x.F` (a bound `x`, not applied further) as `H.F x` when Lean prints `H.F` without dot notation. */
  function noDotNames(n, typeOfName) {
    if (!n || typeof n !== 'object') return n;
    if (n.k === 'app') {
      // An applied `x.F a` keeps its form (the receiver needn't be the first argument).
      const f = n.f && n.f.k === 'id' ? n.f : noDotNames(n.f, typeOfName);
      return Object.assign({}, n, { f, args: n.args.map(a => noDotNames(a, typeOfName)) });
    }
    const m = tWithChildren(n, tChildren(n).map(c => noDotNames(c, typeOfName)));
    if (m.k !== 'id' || !typeOfName) return m;
    const segs = m.v.split('.');
    if (segs.length !== 2 || !LOCAL_NAME.test(segs[0])) return m;
    const ty = typeOfName(segs[0]);
    const head = ty && !/^[:({[⦃]/.test(ty.trim()) && topColon(ty) === -1 ? typeHead(ty, null) : null;
    return head && PP_NODOT.has(`${head}.${segs[1]}`) ? { k: 'app', f: { k: 'id', v: `${head}.${segs[1]}` }, args: [{ k: 'id', v: segs[0] }] } : m;
  }

  /** Inside a type Lean prints `fun` binders without their types: `fun (i : ι) ↦ b` is `fun i ↦ b`. */
  function plainFunBinders(n) {
    if (!n || typeof n !== 'object') return n;
    const m = tWithChildren(n, tChildren(n).map(plainFunBinders));
    // So does `∃` (a `fun` inside): `∃ n : ℕ, p n` is `∃ n, p n`. (One binder group: a later
    // `(h : P x)` would print `∃ (_ : P x)`.)
    if (m.k === 'bind' && (m.head === '∃' || m.head === '∃!')) {
      const b = m.binders.trim();
      if (binderParts(b).op) return m;
      const one = b.match(/^\(?\s*([^\s:(){}⦃⦄[\]]+(?:\s+[^\s:(){}⦃⦄[\]]+)*)\s*:\s*([^()]*(?:\([^()]*\)[^()]*)*?)\s*\)?$/);
      if (one && (b.startsWith('(') === b.endsWith(')')) && (!b.startsWith('(') || matchClose(b, 0) === b.length - 1)) {
        return Object.assign({}, m, { binders: one[1] });
      }
      return m;
    }
    if (m.k !== 'bind' || (m.head !== 'fun' && m.head !== 'λ')) return m;
    const groups = [...m.binders.matchAll(/\(\s*([^():]+?)\s*:[^()]*(?:\([^()]*\)[^()]*)*\)|([^\s()]+)/g)];
    if (!groups.length || groups.map(g => g[0]).join('').replace(/\s+/g, '') !== m.binders.replace(/\s+/g, '')) return m;
    return Object.assign({}, m, { binders: groups.map(g => g[1] || g[2]).join(' ') });
  }

  /**
   * `f i (x i)` with `f : (i : ι) → s i →ₗ[R] t i`: after `i`, `f i` is a bundled map applied
   * through a coercion, which Lean prints `(f i) (x i)`.
   */
  function coerceApps(n, typeOfName) {
    if (!n || typeof n !== 'object') return n;
    let m = tWithChildren(n, tChildren(n).map(c => coerceApps(c, typeOfName)));
    if (m.k !== 'app' || tCore(m.f).k !== 'id' || m.f.coeFn) return m;
    // The head's type: a local's, or a declaration's signature (its explicit parameters).
    let known = typeOfName(tCore(m.f).v) || '';
    let explicit = 0;
    if (isSignature(known)) {
      const peeled = peelSignature(known);
      explicit = peeled.binders.filter(x => x.explicit).reduce((acc, x) => acc + Math.max(1, x.names.length), 0);
      known = peeled.concl;
    }
    let t = tCore(parseTerm(known));
    const args = m.args.filter(a => a.k !== 'named');
    const named = m.args.length - args.length;
    for (let k = explicit; t && k < args.length; k++) {
      if (isBundledType(t)) {
        // From here the map is applied through the coercion: `(f a) b`, or `f b` for a name.
        if (k > 0) return Object.assign({}, m, { f: { k: 'app', f: m.f, args: m.args.slice(0, k + named), coeFn: true }, args: m.args.slice(k + named) });
        const cod = t.k === 'bin' ? t.r : funLikeCodomain(t);
        t = cod ? tCore(cod) : null;
        continue;
      }
      if (t.k === 'bin' && t.op === '→') t = tCore(t.r);
      else if (t.k === 'bind' && (t.head === 'Π' || t.head === '∀')) t = tCore(t.body);
      else return m;
    }
    return m;
  }

  /** Split `f a (b c) d` into ['f', 'a', '(b c)', 'd'] at bracket depth 0. */
  function splitApp(text) {
    const parts = [];
    let depth = 0;
    let cur = '';
    for (const ch of text.trim()) {
      if (OPENERS[ch]) depth++;
      else if (CLOSERS.has(ch)) depth = Math.max(0, depth - 1);
      if (ch === ' ' && depth === 0) {
        if (cur) parts.push(cur);
        cur = '';
      } else {
        cur += ch;
      }
    }
    if (cur) parts.push(cur);
    return parts;
  }

  const T_START = /[A-Za-z_Ͱ-ΟΡ΢Τ-κμ-Ͽἀ-῿℀-⅏\u{1D400}-\u{1D7FF}]/u;

  const T_CONT = /[A-Za-z0-9_'!?Ͱ-ΟΡ΢Τ-κμ-Ͽἀ-῿₀-ₜᵢ-ᵪ℀-⅏\u{1D400}-\u{1D7FF}]/u;

  const T_OPS = ["⁻¹'", "''", "∑'", "∏'", '[[', ']]', '×ˢ', '×ℂ', '⁻¹', ':=', '<|', '|>', '=>', '∃!', '<-', '↔', '→', '←', '∧', '∨', '¬', '≠', '≤', '≥',
    '∈', '∉', '⊆', '⊂', '⊇', '⊃', '∩', '∪', '⊓', '⊔', '•', '∘', '∣', '×', 'ᶜ', '↑', '⇑', '↦', '‖', '⟨', '⟩',
    '(', ')', '[', ']', '{', '}', ',', '|', '+', '-', '*', '/', '%', '^', '=', '<', '>', '\\', '∑', '∏', '∫',
    '∀', '∃', '⋃', '⋂', '⨆', '⨅', 'λ', 'Π', '·', ':', '∞', '⊤', '⊥', '∅', '√'];

  // [precedence, associativity] as in Lean / Mathlib.
  const T_BIN = {
    '<|': [10, 'r'], '|>': [10, 'l'], '↔': [20, 'n'], '→': [25, 'r'], '≃': [25, 'r'], '↪': [25, 'r'], '∨': [30, 'r'], '⊕': [30, 'r'], '∧': [35, 'r'], '×': [35, 'r'],
    '=': [50, 'n'], '≠': [50, 'n'], '<': [50, 'n'], '>': [50, 'n'], '≤': [50, 'n'], '≥': [50, 'n'],
    '∈': [50, 'n'], '∉': [50, 'n'], '⊆': [50, 'n'], '⊂': [50, 'n'], '⊇': [50, 'n'], '⊃': [50, 'n'], '∣': [50, 'n'],
    '∪': [65, 'l'], '+': [65, 'l'], '-': [65, 'l'], '⊔': [68, 'l'], '⊓': [69, 'l'],
    '∩': [70, 'l'], '*': [70, 'l'], '/': [70, 'l'], '%': [70, 'l'], '\\': [70, 'l'], '×ℂ': [72, 'l'],
    '•': [73, 'r'], '^': [75, 'r'], '▸': [75, 'r'], "''": [80, 'l'], "⁻¹'": [80, 'l'], '×ˢ': [82, 'r'], '∘': [90, 'r']
  };
  Object.setPrototypeOf(T_BIN, null);

  // Bundled-map arrows (`→ₗ[R]`, `≃+*`), compositions (`∘ₛₗ`) and tensor products (`⊗[R]`) as
  // one operator token; a bracket index is the token's `idx` (`_` in the spelling).
  const T_MAP_OPS = Object.keys(ARROW_HEADS).filter(k => k.length > 1 && k !== '->')
    .concat(['∘ₗ', '∘ₛₗ', '∘L', '≪≫ₗ', '⊗[_]', '⊗ₜ[_]', '⊗ₜ', '⊗', '⨂[_]', '⨂ₜ[_]'])
    .sort((x, y) => y.length - x.length);
  for (const k of T_MAP_OPS) {
    if (/^(∘|≪≫)/.test(k)) T_BIN[k] = [80, k.startsWith('≪≫') ? 'l' : 'r'];
    else if (k.startsWith('⊗')) T_BIN[k] = [100, 'l'];
    else if (!k.startsWith('⨂')) T_BIN[k] = [25, 'r'];
  }

  // Linear notations are their semilinear ones at `RingHom.id R`; Lean prints them that way.
  const SEMI_OF = { '→ₗ[_]': '→ₛₗ[_]', '≃ₗ[_]': '≃ₛₗ[_]', '→ₘₗ[_]': '→ₘₛₗ[_]', '→L[_]': '→SL[_]', '≃L[_]': '≃SL[_]', '∘ₗ': '∘ₛₗ' };
  Object.setPrototypeOf(SEMI_OF, null);

  const LINEAR_OF = Object.fromEntries(Object.entries(SEMI_OF).map(([k, v]) => [v, k]));

  const T_BINDER_HEADS = new Set(['∀', '∃', '∃!', '∑', '∏', "∑'", "∏'", '⋃', '⋂', '⨆', '⨅', '∫', 'λ', 'Π', '⨂[_]', '⨂ₜ[_]', '⨁']);

  // Precedence of a binder notation's body (Mathlib: `∑ x ∈ s, f x` takes `term:67`, `∫ … , r:60`).
  const T_BODY_PREC = { '∑': 67, '∏': 67, "∑'": 67, "∏'": 67, '∫': 60, '⋃': 60, '⋂': 60, '⨆': 60, '⨅': 60 };
  Object.setPrototypeOf(T_BODY_PREC, null);

  const T_STOP_WORDS = new Set(['at', 'with', 'from', 'by', 'using', 'then', 'else', 'in', 'do']);

  // Syntax that isn't modelled: a term containing it doesn't parse (rather than misparse).
  const T_UNMODELLED = new Set(['if', 'match', 'let', 'have', 'show', 'calc', 'return', 'suffices']);

  const T_OPENERS = ['(', '[', '{', '⟨', '[['];

  const T_CLOSERS = [')', ']', '}', '⟩', ']]'];

  function tokenizeTerm(text) {
    const chars = Array.from(text);
    const toks = [];
    let off = 0;
    const offs = chars.map(c => { const o = off; off += c.length; return o; });
    offs.push(off);
    let i = 0;
    while (i < chars.length) {
      const c = chars[i];
      if (/\s/.test(c)) { i++; continue; }
      let j = i;
      if (/[0-9]/.test(c)) {
        while (j < chars.length && (/[0-9]/.test(chars[j]) || (chars[j] === '.' && /[0-9]/.test(chars[j + 1] || '')))) j++;
        toks.push({ k: 'num', v: chars.slice(i, j).join(''), s: offs[i], e: offs[j] });
      } else if (T_START.test(c)) {
        j = i + 1;
        for (;;) {
          while (j < chars.length && T_CONT.test(chars[j])) j++;
          if (chars[j] === '.' && j + 1 < chars.length && (T_START.test(chars[j + 1]) || /[0-9]/.test(chars[j + 1]))) { j += 2; continue; }
          break;
        }
        if (chars[j] === '*' && /^(Type|Sort)$/.test(chars.slice(i, j).join(''))) j++; // `Type*`
        toks.push({ k: 'id', v: chars.slice(i, j).join(''), s: offs[i], e: offs[j] });
      } else if (c === '?' && i + 1 < chars.length && T_START.test(chars[i + 1])) {
        // A hole / metavariable `?_`, `?x`.
        j = i + 1;
        while (j < chars.length && T_CONT.test(chars[j])) j++;
        toks.push({ k: 'id', v: chars.slice(i, j).join(''), s: offs[i], e: offs[j] });
      } else if (c === '.' && i + 1 < chars.length && (T_START.test(chars[i + 1]) || /[0-9]/.test(chars[i + 1]))) {
        j = i + 1;
        while (j < chars.length && T_CONT.test(chars[j])) j++;
        toks.push({ k: 'field', v: chars.slice(i + 1, j).join(''), s: offs[i], e: offs[j] });
      } else if (T_MAP_START.test(c) && (j = tMapOp(chars, i, toks, offs)) > i) {
        // a bundled-map operator (pushed by tMapOp)
      } else {
        const ahead = chars.slice(i, i + 3).join('');
        const op = T_OPS.find(o => ahead.startsWith(o)) || c;
        j = i + Array.from(op).length;
        toks.push({ k: 'op', v: op, s: offs[i], e: offs[j] });
      }
      i = j;
    }
    return toks;
  }

  const T_MAP_START = /[→≃↪∘≪⊗⨂]/;

  // Each spelling split once: { sp, pre: chars before the hole, close: the hole's closer }, by first character.
  const T_MAP_BY_FIRST = new Map();
  for (const sp of T_MAP_OPS) {
    const hole = sp.indexOf('_');
    const entry = { sp, pre: Array.from(hole === -1 ? sp : sp.slice(0, hole)), close: hole === -1 ? null : Array.from(sp.slice(hole + 1))[0] };
    if (!T_MAP_BY_FIRST.has(entry.pre[0])) T_MAP_BY_FIRST.set(entry.pre[0], []);
    T_MAP_BY_FIRST.get(entry.pre[0]).push(entry);
  }

  /** A bundled-map operator at `chars[i]`: push its token and return the index after it, or i. */
  function tMapOp(chars, i, toks, offs) {
    for (const { sp, pre, close } of T_MAP_BY_FIRST.get(chars[i]) || []) {
      if (pre.some((ch, k) => chars[i + k] !== ch)) continue;
      let j = i + pre.length;
      let idx = null;
      if (close !== null) {
        const open = pre[pre.length - 1];
        let depth = 0, k = j;
        for (; k < chars.length; k++) {
          if (chars[k] === open) depth++;
          else if (chars[k] === close) { if (depth === 0) break; depth--; }
        }
        if (k >= chars.length) continue;
        idx = chars.slice(j, k).join('').trim();
        j = k + 1;
      } else if (T_CONT.test(chars[j] || '') && !/[0-9]/.test(chars[j])) {
        continue; // `→ₗ` is a prefix of a longer spelling we don't know: not this operator
      }
      toks.push({ k: 'op', v: sp, idx, s: offs[i], e: offs[j] });
      return j;
    }
    return i;
  }

  const tPeek = (st) => st.toks[st.i];

  const tNext = (st) => st.toks[st.i++];

  const tIs = (t, v) => Boolean(t) && t.k === 'op' && t.v === v;

  // Parse failures throw this (cheap: no stack trace); `parseTerm` turns it into null.
  const T_FAIL = Object.freeze({ fail: true });

  function tExpect(st, v) { if (!tIs(tNext(st), v)) throw T_FAIL; }

  /**
   * A small least-recently-used cache for pure functions of a string (parsing is repeated a
   * lot: the same binder types and signatures come back across declarations and hovers).
   */
  function memoized(fn, limit = 4000) {
    const cache = new Map();
    return (key) => {
      if (cache.has(key)) {
        const v = cache.get(key);
        cache.delete(key);
        cache.set(key, v);
        return v;
      }
      const v = fn(key);
      cache.set(key, v);
      if (cache.size > limit) cache.delete(cache.keys().next().value);
      return v;
    };
  }

  /**
   * Parse a Lean term into a small AST, or null if it uses notation we don't model. Results
   * are shared (memoized): callers must not change them.
   */
  const parseTerm = memoized((text) => {
    if (typeof text !== 'string') return null;
    const st = { src: text, toks: tokenizeTerm(text), i: 0 };
    try {
      const node = tExpr(st, 0);
      return st.i === st.toks.length ? node : null;
    } catch (err) {
      if (err !== T_FAIL) throw err;
      return null;
    }
  });

  /** Source text of the tokens up to a top-level stop token (left unconsumed). */
  function tRawUntil(st, stops) {
    const first = st.i;
    let depth = 0;
    while (st.i < st.toks.length) {
      const t = tPeek(st);
      if (t.k === 'op') {
        if (depth === 0 && stops.includes(t.v)) break;
        if (T_OPENERS.includes(t.v)) depth++;
        else if (T_CLOSERS.includes(t.v)) { if (depth === 0) break; depth--; }
      }
      st.i++;
    }
    return st.i > first ? st.src.slice(st.toks[first].s, st.toks[st.i - 1].e).trim() : '';
  }

  function tStartsArg(t) {
    if (!t) return false;
    if (t.k === 'num') return true;
    if (t.k === 'id') return !T_STOP_WORDS.has(t.v);
    return t.k === 'op' && ['(', '⟨', '{', '[[', '↑', '⇑', '·', '∞', '⊤', '⊥', '∅'].includes(t.v);
  }

  function tBinder(st, head, idx = null) {
    const stops = head === 'fun' || head === 'λ' ? ['=>', '↦'] : [','];
    let binders = tRawUntil(st, stops);
    // `∀ f : Π i, s i, P`: a binder type with binders of its own keeps their commas.
    while (stops[0] === ',' && innerCommas(binders) > 0 && tIs(tPeek(st), ',')) {
      tNext(st);
      binders += ', ' + tRawUntil(st, stops);
    }
    const sep = tNext(st);
    if (!sep || sep.k !== 'op' || !stops.includes(sep.v)) throw T_FAIL;
    const node = { k: 'bind', head, binders, sep: sep.v, body: tExpr(st, T_BODY_PREC[head] || 0) };
    if (idx !== null) node.idx = parseTerm(idx) || { k: 'raw', v: idx };
    return node;
  }

  /** Commas still owed to binders inside a binder's type (`f : Π i` owes one), at depth 0. */
  function innerCommas(binders) {
    const c = binders.search(/:(?!=)/);
    if (c === -1) return 0;
    const type = binders.slice(c + 1);
    let owed = 0;
    for (let k = 0, depth = 0; k < type.length; k++) {
      const ch = type[k];
      if (OPENERS[ch]) depth++;
      else if (CLOSERS.has(ch)) depth = Math.max(0, depth - 1);
      else if (depth === 0 && ch === ',') owed--;
      else if (depth === 0 && /[ΠΣ∀∃∑∏⋃⋂⨆⨅]/.test(ch) && !/[\w'.]/.test(type[k - 1] || ' ')) owed++;
    }
    return owed;
  }

  // Source spans: `span` is [start, end) of a node in the parsed text; a parenthesised term
  // also has `pspan`, its span including the parentheses (hovering a bracket shows the term).
  const tSpan = (n) => n.pspan || n.span;

  function tPrefix(st) {
    const first = st.i;
    const node = tPrefixBody(st);
    const span = [st.toks[first].s, st.toks[st.i - 1].e];
    return node.paren ? Object.assign(node, { pspan: span }) : Object.assign(node, { span });
  }

  function tPrefixBody(st) {
    const t = tNext(st);
    if (!t) throw T_FAIL;
    if (t.k === 'num') return { k: 'num', v: t.v };
    if (t.k === 'id') {
      if (t.v === 'fun') return tBinder(st, 'fun');
      if (t.v === 'by') {
        // A tactic block inside a term (`⟨by simp, h⟩`, `(by positivity)`): opaque text.
        const body = tRawUntil(st, [',']);
        return { k: 'raw', v: body ? `by ${body}` : 'by', loose: true };
      }
      if (T_STOP_WORDS.has(t.v) || T_UNMODELLED.has(t.v)) throw T_FAIL;
      // `C(X, Y)`, `SL(2, ℤ)`: notation with its parenthesis right after the name (an
      // application has a space); kept as written.
      const nx = tPeek(st);
      if (nx && nx.v === '(' && nx.s === t.e && t.e !== undefined) {
        tNext(st);
        const inner = tRawUntil(st, []);
        tExpect(st, ')');
        return { k: 'raw', v: `${t.v}(${inner})` };
      }
      return { k: 'id', v: t.v };
    }
    if (t.k === 'field') throw T_FAIL;
    switch (t.v) {
      case '¬': return { k: 'pre', op: '¬', e: tExpr(st, 40) };
      case '-': return { k: 'pre', op: '-', e: tExpr(st, 75) };
      case '↑': case '⇑': return { k: 'pre', op: t.v, e: tArg(st) };
      case '√': return { k: 'pre', op: '√', e: tExpr(st, 100) }; // `prefix:100 "√" => Real.sqrt`
      case '(': {
        const t1 = tPeek(st), t2 = st.toks[st.i + 1];
        if (t1 && t1.k === 'id' && tIs(t2, ':=')) {
          // A named argument `(x := v)`.
          st.i += 2;
          const value = tExpr(st, 0);
          tExpect(st, ')');
          return { k: 'named', name: t1.v, value };
        }
        const e = tExpr(st, 0);
        if (tIs(tPeek(st), ':')) { tNext(st); const ty = tExpr(st, 0); tExpect(st, ')'); return { k: 'asc', e, ty }; }
        if (tIs(tPeek(st), ',')) {
          // A pair `(a, b)` (`Prod.mk`): a tuple printed in parentheses.
          const es = [e];
          while (tIs(tPeek(st), ',')) { tNext(st); es.push(tExpr(st, 0)); }
          tExpect(st, ')');
          return { k: 'tuple', es, pair: true };
        }
        tExpect(st, ')');
        return Object.assign({}, e, { paren: true }); // `(f ∘ g) x`: parenthesised terms can be applied
      }
      case '|': { const e = tExpr(st, 0); tExpect(st, '|'); return { k: 'abs', e }; }
      case '‖': { const e = tExpr(st, 0); tExpect(st, '‖'); return { k: 'norm', e }; }
      case '⟨': {
        const es = [];
        if (!tIs(tPeek(st), '⟩')) {
          for (;;) { es.push(tExpr(st, 0)); if (tIs(tPeek(st), ',')) { tNext(st); continue; } break; }
        }
        tExpect(st, '⟩');
        return { k: 'tuple', es };
      }
      case '{': { const inner = tRawUntil(st, []); tExpect(st, '}'); return { k: 'raw', v: `{${inner}}` }; }
      case '[': { const inner = tRawUntil(st, []); tExpect(st, ']'); return { k: 'raw', v: `[${inner}]` }; }
      case '[[': {
        const a = tExpr(st, 0); tExpect(st, ',');
        const b = tExpr(st, 0); tExpect(st, ']]');
        return { k: 'app', f: { k: 'id', v: 'Set.uIcc' }, args: [a, b] };
      }
      case '·': case '∞': case '⊤': case '⊥': case '∅': return { k: 'id', v: t.v };
      default:
        if (T_BINDER_HEADS.has(t.v)) return tBinder(st, t.v, t.idx === undefined ? null : t.idx);
        throw T_FAIL;
    }
  }

  function tPostfix(st, e) {
    for (;;) {
      const t = tPeek(st);
      if (tIs(t, '⁻¹') || tIs(t, 'ᶜ')) { tNext(st); e = { k: 'post', op: t.v, e, span: [tSpan(e)[0], t.e] }; continue; }
      if (t && t.k === 'field') { tNext(st); e = { k: 'proj', e, f: t.v, span: [tSpan(e)[0], t.e] }; continue; }
      return e;
    }
  }

  function tArg(st) { return tPostfix(st, tPrefix(st)); }

  function tExpr(st, minPrec) {
    let left = tArg(st);
    for (;;) {
      const t = tPeek(st);
      if (!t) break;
      if (t.k === 'op' && T_BIN[t.v]) {
        const [p, assoc] = T_BIN[t.v];
        if (p < minPrec) break;
        tNext(st);
        const right = tExpr(st, assoc === 'r' ? p : p + 1);
        const span = [tSpan(left)[0], tSpan(right)[1]];
        const binder = t.v === '→' ? arrowBinder(left) : null;
        if (binder) { left = { k: 'bind', head: 'Π', arrow: true, binders: binder, sep: '→', body: right, span }; continue; }
        left = { k: 'bin', op: t.v, l: left, r: right, span };
        if (t.idx) left.idx = parseTerm(t.idx) || { k: 'raw', v: t.idx };
        continue;
      }
      const applicable = ['id', 'app', 'proj'].includes(left.k) || left.paren || (left.k === 'pre' && (left.op === '↑' || left.op === '⇑'));
      if (minPrec <= 1024 && applicable && tStartsArg(t)) {
        const arg = tArg(st);
        const span = [tSpan(left)[0], tSpan(arg)[1]];
        left = left.k === 'app' && !left.paren
          ? { k: 'app', f: left.f, args: left.args.concat([arg]), span }
          : { k: 'app', f: left, args: [arg], span };
        continue;
      }
      break;
    }
    return left;
  }

  /** `(x y : A)` / `{x : A}` / `[C x]` before `→`: the binder of a dependent arrow, or null. */
  function arrowBinder(n) {
    if (n.k === 'asc') {
      const names = n.e.k === 'id' ? [n.e] : n.e.k === 'app' && !n.e.paren ? [n.e.f, ...n.e.args] : null;
      if (names && names.every(x => x.k === 'id' && /^[^.?]+$/.test(x.v))) return `(${names.map(x => x.v).join(' ')} : ${showTerm(n.ty)})`;
      return null;
    }
    if (n.k === 'raw' && (/^\{[^{}:]+:[\s\S]+\}$/.test(n.v) || /^\[[\s\S]+\]$/.test(n.v))) return n.v;
    return null;
  }

  function tPrec(n) {
    switch (n.k) {
      case 'bin': return T_BIN[n.op][0];
      case 'pre': return n.op === '¬' ? 40 : n.op === '-' ? 75 : n.op === '√' ? 100 : 2000;
      case 'post': return 1100;
      case 'app': return 1024;
      case 'bind': return n.arrow ? 25 : T_BODY_PREC[n.head] || 0; // `∑ i ∈ s, f i ≤ c`: the body stops at `≤`
      case 'raw': return n.loose ? 0 : 2000; // text we couldn't parse: parenthesise when nested
      default: return 2000;
    }
  }

  /**
   * Print an AST back to Lean text, adding parentheses only where precedence needs them.
   * `trailing`: nothing follows the term, so a binder notation at the end needs none
   * (`a = ∑ i ∈ s, f i`, `M →ₗ[R] ⨂[R] i, s i`, `tprod R fun i ↦ f i`), as Lean prints it.
   */
  function showTerm(n, minPrec = 0, trailing = true) {
    // (A dependent arrow `(i : ι) → s i` is an infix of precedence 25: `R × ((i : ι) → s i)`.)
    const openEnded = n.k === 'bind' && !n.arrow && (minPrec <= 1024 || n.head === 'fun' || n.head === 'λ');
    const paren = tPrec(n) < minPrec && !(trailing && openEnded);
    const tr = paren || trailing;
    let s;
    switch (n.k) {
      case 'id': case 'num': case 'raw': s = n.v; break;
      case 'asc': s = `(${showTerm(n.e)} : ${showTerm(n.ty)})`; break;
      case 'abs': s = `|${showTerm(n.e)}|`; break;
      case 'norm': s = `‖${showTerm(n.e)}‖`; break;
      case 'tuple': s = n.pair ? `(${n.es.map(e => showTerm(e)).join(', ')})` : `⟨${n.es.map(e => showTerm(e)).join(', ')}⟩`; break;
      case 'named': s = `(${n.name} := ${showTerm(n.value)})`; break;
      case 'proj': s = `${showTerm(n.e, 1025, false)}.${n.f}`; break;
      case 'post': s = `${showTerm(n.e, 1025, false)}${n.op}`; break;
      case 'pre':
        s = n.op === '¬' ? `¬${showTerm(n.e, 40, tr)}` : n.op === '-' ? `-${showTerm(n.e, 75, tr)}`
          : n.op === '√' ? `√${showTerm(n.e, 100, tr)}` : `${n.op}${showTerm(n.e, 1025, tr)}`;
        break;
      case 'app': {
        const so = n.f.k === 'id' && (n.f.v === 'Type' || n.f.v === 'Sort') && n.args.length === 1 ? sortText(n.f.v, n.args[0]) : null;
        if (so) { s = so; break; }
        // `(liftAux φ) x`: a coerced map (or one written in parentheses) keeps them.
        const head = showTerm(n.f, n.f.coeFn || (n.f.paren && n.f.k === 'app') ? 1025 : 1024, false);
        const last = n.args[n.args.length - 1];
        if (!tr && last && last.k === 'bind' && !last.arrow) {
          // A `fun` (or other binder) as the last argument with more to follow: Lean puts the
          // parentheses around the application, `(f fun i ↦ g i) = …`.
          s = `(${[head, ...n.args.slice(0, -1).map(a => showTerm(a, 1025, false)), showTerm(last, 1025, true)].join(' ')})`;
          break;
        }
        s = [head, ...n.args.map((a, i) => showTerm(a, 1025, i === n.args.length - 1 ? tr : false))].join(' ');
        break;
      }
      case 'bin': {
        const [p, assoc] = T_BIN[n.op];
        const id = n.idx && LINEAR_OF[n.op] && tCore(n.idx).k === 'app' && tCore(n.idx).f.k === 'id' && tCore(n.idx).f.v === 'RingHom.id' &&
          tCore(n.idx).args.length === 1 ? tCore(n.idx).args[0] : null;
        const op = id ? LINEAR_OF[n.op].replace('_', showTerm(id)) : n.idx ? n.op.replace('_', showTerm(n.idx)) : n.op;
        s = `${showTerm(n.l, assoc === 'l' ? p : p + 1, false)} ${op} ${showTerm(n.r, assoc === 'r' ? p : p + 1, tr)}`;
        break;
      }
      case 'bind':
        if (n.arrow) { s = `${n.binders} → ${showTerm(n.body, 25, tr)}`; break; }
        s = n.head === 'fun' || n.head === 'λ'
          ? `fun ${n.binders} ${n.sep} ${showTerm(n.body, 0, tr)}`
          : `${n.idx ? n.head.replace('_', showTerm(n.idx)) : n.head} ${n.binders}, ${showTerm(n.body, T_BODY_PREC[n.head] || 0, tr)}`;
        break;
      default: s = '?';
    }
    return paren ? `(${s})` : s;
  }

  // Ascriptions `(0 : ℝ)` and coercion arrows don't change which term is meant.
  function tCore(n) {
    while (n && (n.k === 'asc' || (n.k === 'pre' && (n.op === '↑' || n.op === '⇑')))) n = n.e;
    return n;
  }

  const tIdEq = (a, b) => a === b || a.endsWith('.' + b) || b.endsWith('.' + a);

  const tRawEq = (a, b) => a.replace(/\s+/g, '') === b.replace(/\s+/g, '');

  function tChildren(n) {
    switch (n.k) {
      case 'app': return [n.f, ...n.args];
      case 'bin': return n.idx ? [n.l, n.r, n.idx] : [n.l, n.r];
      case 'pre': case 'post': case 'abs': case 'norm': case 'proj': case 'asc': return [n.e];
      case 'tuple': return n.es;
      case 'bind': return n.idx ? [n.body, n.idx] : [n.body];
      case 'named': return [n.value];
      default: return [];
    }
  }

  function tWithChildren(n, kids) {
    switch (n.k) {
      case 'app': return Object.assign({}, n, { f: kids[0], args: kids.slice(1) });
      case 'bin': return Object.assign({}, n, { l: kids[0], r: kids[1] }, n.idx ? { idx: kids[2] } : {});
      case 'pre': case 'post': case 'abs': case 'norm': case 'proj': case 'asc': return Object.assign({}, n, { e: kids[0] });
      case 'tuple': return Object.assign({}, n, { es: kids });
      case 'bind': return Object.assign({}, n, { body: kids[0] }, n.idx ? { idx: kids[1] } : {});
      case 'named': return Object.assign({}, n, { value: kids[0] });
      default: return n;
    }
  }

  /**
   * Match pattern `p` (variables in `vars`) against term `t`, extending `sub` (Map name → node).
   * `x.field` with `x` a variable matches `t.field` (dot notation in lemma statements).
   */
  function matchTerm(p, t, vars, sub, bound = null) {
    const tp = tCore(p), tt = tCore(t);
    if (!tp || !tt) return false;
    // `?β a` with `a` bound by an enclosing binder, against any term: `β := fun a ↦ term`
    // (Lean's higher-order pattern unification), when matching it first-order fails.
    if (bound && tp.k === 'app' && tp.f.k === 'id' && vars.has(tp.f.v) && !sub.has(tp.f.v) &&
        tp.args.every(a => tCore(a).k === 'id' && bound.has(tCore(a).v)) && new Set(tp.args.map(a => tCore(a).v)).size === tp.args.length) {
      const trial = new Map(sub);
      if (!(tt.k === 'app' && tt.args.length === tp.args.length && matchTerm(tp.f, tt.f, vars, trial, bound) &&
            tp.args.every((e, i) => matchTerm(e, tt.args[i], vars, trial, bound)))) {
        const names = tp.args.map(a => tCore(a).v);
        const tb = tCore(t);
        const fa = tb && tb.k === 'app' ? flatApp(tb) : null;
        // `fun e' ↦ f e'` is just `f` (when `f` doesn't mention the bound names).
        const eta = fa && fa.args.length >= names.length &&
          fa.args.slice(-names.length).every((a, i) => tCore(a).k === 'id' && tCore(a).v === names[i]) &&
          ![fa.f, ...fa.args.slice(0, -names.length)].some(x => names.some(nm => freeNames(x).has(nm)));
        const head = eta && (fa.args.length === names.length ? fa.f : { k: 'app', f: fa.f, args: fa.args.slice(0, -names.length) });
        sub.set(tp.f.v, head || { k: 'bind', head: 'fun', binders: names.join(' '), sep: '↦', body: t });
        return true;
      }
    }
    if (tp.k === 'id') {
      if (vars.has(tp.v)) {
        if (sub.has(tp.v)) return sameTerm(sub.get(tp.v), t);
        sub.set(tp.v, t);
        return true;
      }
      const dot = tp.v.indexOf('.');
      if (dot > 0 && vars.has(tp.v.slice(0, dot))) {
        const rest = tp.v.slice(dot + 1);
        let recv = null;
        if (tt.k === 'id' && tt.v.endsWith('.' + rest) && tt.v.length > rest.length + 1) recv = { k: 'id', v: tt.v.slice(0, tt.v.length - rest.length - 1) };
        else if (tt.k === 'proj' && tt.f === rest) recv = tt.e;
        return Boolean(recv) && matchTerm({ k: 'id', v: tp.v.slice(0, dot) }, recv, vars, sub, bound);
      }
    }
    // `n.succ` written as one identifier vs. a projection node of `n`.
    if (tp.k === 'proj' && tt.k === 'id' && tt.v.endsWith('.' + tp.f) && tt.v.length > tp.f.length + 1) {
      return matchTerm(tp.e, { k: 'id', v: tt.v.slice(0, tt.v.length - tp.f.length - 1) }, vars, sub, bound);
    }
    if (tp.k === 'id' && tt.k === 'proj' && tp.v.endsWith('.' + tt.f) && tp.v.length > tt.f.length + 1) {
      return matchTerm({ k: 'id', v: tp.v.slice(0, tp.v.length - tt.f.length - 1) }, tt.e, vars, sub, bound);
    }
    // Universes: `Type u` against `Type u_4` fixes `u`; levels we can't compare don't block a match.
    const sp = sortOf(tp), st = sortOf(tt);
    if (sp || st) {
      if (!sp || !st) return false;
      const bind = (level, target) => {
        const v = level && tCore(level);
        if (v && v.k === 'id' && vars.has(v.v) && !sub.has(v.v) && target) sub.set(v.v, target);
        return true;
      };
      if (sp.kind === 'Prop' || st.kind === 'Prop') return sp.kind === st.kind || (sp.kind === 'Sort' && bind(sp.level, { k: 'num', v: '0' }));
      if (!sp.level || !st.level) return true;
      return bind(sp.level, sp.kind === st.kind ? st.level : sp.kind === 'Sort' ? levelSucc(st.level) : levelPred(st.level));
    }
    if (tp.k !== tt.k) return false;
    switch (tp.k) {
      case 'id': return tIdEq(tp.v, tt.v);
      case 'num': return tp.v === tt.v;
      case 'raw': return tRawEq(tp.v, tt.v);
      case 'abs': case 'norm': return matchTerm(tp.e, tt.e, vars, sub, bound);
      case 'pre': case 'post': return tp.op === tt.op && matchTerm(tp.e, tt.e, vars, sub, bound);
      case 'proj': return tp.f === tt.f && matchTerm(tp.e, tt.e, vars, sub, bound);
      case 'tuple': return tp.es.length === tt.es.length && tp.es.every((e, i) => matchTerm(e, tt.es[i], vars, sub, bound));
      case 'app': {
        // `(f a) b` is `f a b` (the parentheses Lean prints around a coerced map don't matter).
        const fp = flatApp(tp), ft = flatApp(tt);
        return fp.args.length === ft.args.length && matchTerm(fp.f, ft.f, vars, sub, bound) &&
          fp.args.every((e, i) => matchTerm(e, ft.args[i], vars, sub, bound));
      }
      case 'bin': {
        let pi = tp.idx, ti = tt.idx;
        if (tp.op !== tt.op) {
          // `M →ₗ[R] N` is `M →ₛₗ[RingHom.id R] N` (and `∘ₗ` is `∘ₛₗ`).
          if (SEMI_OF[tt.op] === tp.op) ti = ti && { k: 'app', f: { k: 'id', v: 'RingHom.id' }, args: [ti] };
          else if (SEMI_OF[tp.op] === tt.op) pi = pi && { k: 'app', f: { k: 'id', v: 'RingHom.id' }, args: [pi] };
          else return false;
        }
        return Boolean(pi) === Boolean(ti) && (!pi || matchTerm(pi, ti, vars, sub, bound)) &&
          matchTerm(tp.l, tt.l, vars, sub, bound) && matchTerm(tp.r, tt.r, vars, sub, bound);
      }
      case 'named': return tp.name === tt.name && matchTerm(tp.value, tt.value, vars, sub, bound);
      case 'bind': {
        const piHead = (h) => (h === '∀' ? 'Π' : h);
        if (piHead(tp.head) !== piHead(tt.head)) return false;
        if (Boolean(tp.idx) !== Boolean(tt.idx) || (tp.idx && !matchTerm(tp.idx, tt.idx, vars, sub, bound))) return false;
        const bp = binderParts(tp.binders), bt = binderParts(tt.binders);
        if (bp.names.length !== bt.names.length || bp.op !== bt.op || (bp.range === null) !== (bt.range === null)) return false;
        if (bp.range !== null) {
          const rp = bp.range.split('..'), rt = bt.range.split('..');
          if (rp.length !== rt.length) return false;
          for (let i = 0; i < rp.length; i++) {
            const a = parseTerm(rp[i]), b = parseTerm(rt[i]);
            if (a && b ? !matchTerm(a, b, vars, sub, bound) : !tRawEq(rp[i], rt[i])) return false;
          }
        }
        // Alpha-equivalence: rename the pattern's bound variables to the target's.
        const ren = new Map(bp.names.map((nm, i) => [nm, { k: 'id', v: bt.names[i] }]));
        return matchTerm(substTerm(tp.body, ren), tt.body, vars, sub, new Set([...(bound || []), ...bt.names]));
      }
      default: return false;
    }
  }

  const sameTerm = (a, b) => matchTerm(a, b, new Set(), new Map());

  /** `(f a) b` as one application `f a b`. */
  function flatApp(n) {
    let f = n.f, args = n.args;
    while (f && f.k === 'app') { args = [...f.args, ...args]; f = f.f; }
    return { f, args };
  }

  // --- Universe levels ---

  /**
   * A constant's signature with its universe parameters written `?u` (as Lean shows universe
   * metavariables), so that they are solved by matching, not taken for the caller's universes.
   */
  function universeParams(sig) {
    if (!sig) return sig;
    const names = new Set();
    // Universe names (`u`, `u_1`, `u\u03b9`).
    for (const m of sig.matchAll(/(?<![\w'.])(?:Type|Sort)\s+(\((?:[^()]|\([^()]*\))*\)|[A-Za-z_\u0370-\u03ff][\w'\u0370-\u03ff\u2080-\u2089]*)/g)) {
      m[1].replace(/(?<![\w'?\u0370-\u03ff])[A-Za-z_\u0370-\u03ff][\w'\u0370-\u03ff\u2080-\u2089]*/g, (u) => { if (u !== 'max' && u !== 'imax') names.add(u); return u; });
    }
    let out = sig;
    names.forEach(u => {
      out = out.replace(/((?:Type|Sort)\s+(?:\((?:[^()]|\([^()]*\))*\)|[A-Za-z_\u0370-\u03ff][\w'\u0370-\u03ff\u2080-\u2089]*))/g,
        (lv) => lv.replace(new RegExp(`(?<![\\w'?\\u0370-\\u03FF])${u}(?![\\w'\\u0370-\\u03FF\\u2080-\\u2089])`, 'g'), `?${u}`));
    });
    return out;
  }

  /** `Type u` / `Sort l` / `Prop` / `Type*`: { kind, level } (level null when unknown), or null. */
  function sortOf(n) {
    n = tCore(n);
    if (!n) return null;
    if (n.k === 'id') {
      if (n.v === 'Prop') return { kind: 'Prop', level: null };
      if (n.v === 'Type') return { kind: 'Type', level: { k: 'num', v: '0' } };
      if (n.v === 'Type*' || n.v === 'Sort*') return { kind: n.v.slice(0, 4), level: null };
      return null;
    }
    if (n.k === 'app' && n.f.k === 'id' && (n.f.v === 'Type' || n.f.v === 'Sort') && n.args.length === 1) return { kind: n.f.v, level: tCore(n.args[0]) };
    return null;
  }

  const levelSucc = (l) => ({ k: 'bin', op: '+', l, r: { k: 'num', v: '1' } });

  const levelPred = (l) => {
    l = tCore(l);
    if (l.k === 'bin' && l.op === '+' && l.r.k === 'num') return Number(l.r.v) === 1 ? l.l : { k: 'bin', op: '+', l: l.l, r: { k: 'num', v: String(Number(l.r.v) - 1) } };
    if (l.k === 'num' && Number(l.v) > 0) return { k: 'num', v: String(Number(l.v) - 1) };
    return null;
  };

  // Levels are ASTs (`u`, `2`, `u + 1`, `max a b`, `imax a b`). Lean keeps a level's shape when
  // it instantiates a constant, with cheap simplifications (`max 1 (u + 1)` is `u + 1`), and
  // prints `Sort (l + 1)` as `Type l`: `Type (max (max u_1 u_4) u_8)`, `Type u_1`.
  const lvlNum = (k) => ({ k: 'num', v: String(k) });

  /** `{ base, k }` for `base + k` (base null for a constant), or null if it isn't a level. */
  function lvlOffset(l) {
    l = tCore(l);
    if (!l) return null;
    if (l.k === 'num') return { base: null, k: Number(l.v) };
    if (l.k === 'bin' && l.op === '+' && tCore(l.r).k === 'num') {
      const o = lvlOffset(l.l);
      return o && { base: o.base, k: o.k + Number(tCore(l.r).v) };
    }
    return { base: l, k: 0 };
  }

  const lvlAdd = (base, k) => (base ? (k ? { k: 'bin', op: '+', l: base, r: lvlNum(k) } : base) : lvlNum(k));

  const lvlArgs = (l) => { l = tCore(l); return l && l.k === 'app' && l.f.k === 'id' && (l.f.v === 'max' || l.f.v === 'imax') ? l.args : null; };

  const lvlKind = (l) => { l = tCore(l); return l && l.k === 'app' && l.f.k === 'id' ? l.f.v : null; };

  /** Is `a ≤ b` for every assignment, by the obvious reasons Lean's simplifier sees? */
  function lvlLeq(a, b) {
    const oa = lvlOffset(a), ob = lvlOffset(b);
    if (!oa || !ob) return false;
    if (!oa.base) return oa.k <= ob.k || (lvlKind(ob.base) === 'max' && lvlArgs(ob.base).some(x => lvlLeq(lvlNum(oa.k - ob.k), x)));
    if (ob.base && oa.k <= ob.k && sameTerm(oa.base, ob.base)) return true;
    const bm = lvlKind(ob.base) === 'max' ? lvlArgs(ob.base) : null;
    return Boolean(bm) && ob.k === 0 && bm.some(x => lvlLeq(a, x));
  }

  /** Simplify a level, keeping its shape (max of two where one is smaller drops it). */
  function lvlSimp(l) {
    l = tCore(l);
    if (!l) return l;
    const args = lvlArgs(l);
    if (args) {
      const parts = args.map(lvlSimp);
      if (lvlKind(l) === 'imax' && parts.length === 2) {
        const o = lvlOffset(parts[1]);
        if (o && !o.base && o.k === 0) return lvlNum(0);
        if (!o || (o.k < 1 && !lvlArgs(parts[1]))) return { k: 'app', f: { k: 'id', v: 'imax' }, args: parts };
      }
      return parts.reduceRight((acc, x) => {
        if (acc === null) return x;
        if (lvlLeq(x, acc)) return acc;
        if (lvlLeq(acc, x)) return x;
        return { k: 'app', f: { k: 'id', v: 'max' }, args: [x, acc] };
      }, null);
    }
    const o = lvlOffset(l);
    if (o && o.base && o.k) return lvlAdd(lvlSimp(o.base), o.k);
    return l;
  }

  /** `l - 1` when every part of `l` is at least 1, else null. */
  function lvlDec(l) {
    const o = lvlOffset(l);
    if (!o) return null;
    if (o.k >= 1) return lvlAdd(o.base, o.k - 1);
    const args = lvlKind(o.base) === 'max' ? lvlArgs(o.base) : null;
    if (!args) return null;
    const dec = args.map(lvlDec);
    return dec.every(Boolean) ? { k: 'app', f: { k: 'id', v: 'max' }, args: dec } : null;
  }

  /** Lean's printing: right-nested `max` flattens (`max a b c`), left-nested keeps parentheses. */
  function lvlShow(l) {
    l = tCore(l);
    const args = lvlArgs(l);
    if (args) {
      const flat = [];
      let cur = l;
      while (lvlKind(cur) === lvlKind(l) && lvlArgs(cur) && lvlArgs(cur).length === 2) { flat.push(lvlArgs(cur)[0]); cur = lvlArgs(cur)[1]; }
      if (lvlArgs(cur) && lvlKind(cur) === lvlKind(l)) flat.push(...lvlArgs(cur)); else flat.push(cur);
      return `${lvlKind(l)} ${flat.map(x => { const t = lvlShow(x); return /\s/.test(t) ? `(${t})` : t; }).join(' ')}`;
    }
    const o = lvlOffset(l);
    if (o && o.base && o.k) return `${lvlShow(o.base)} + ${o.k}`;
    return showTerm(l);
  }

  const isLevel = (l) => {
    l = tCore(l);
    if (!l) return false;
    if (l.k === 'num') return true;
    if (l.k === 'id') return /^\??[A-Za-z_Ͱ-Ͽ][\w'Ͱ-Ͽ₀-₉]*$/.test(l.v) && l.v !== 'max' && l.v !== 'imax';
    if (l.k === 'bin') return l.op === '+' && isLevel(l.l) && tCore(l.r).k === 'num';
    return Boolean(lvlArgs(l)) && lvlArgs(l).every(isLevel);
  };

  /** `Sort (max 1 (u + 1))` as Lean prints it: `Type u`; `Sort 0` is `Prop`. Text, or null. */
  function sortText(kind, level) {
    if (!isLevel(level)) return null;
    const l = lvlSimp(kind === 'Type' ? lvlAdd(level, 1) : level);
    const o = lvlOffset(l);
    if (o && !o.base && o.k === 0) return 'Prop';
    const d = lvlDec(l);
    if (d) { const t = lvlShow(lvlSimp(d)); return t === '0' ? 'Type' : `Type ${/\s/.test(t) ? `(${t})` : t}`; }
    const t = lvlShow(l);
    return `Sort ${/\s/.test(t) ? `(${t})` : t}`;
  }

  /** The level of a pi type with this binder sort and body sort (`imax`), as text, or null. */
  function piSort(binderSort, bodySort) {
    const b = sortOf(parseTerm(binderSort || '')), r = sortOf(parseTerm(bodySort || ''));
    if (!b || !r) return null;
    if (r.kind === 'Prop') return 'Prop';
    if (!b.level || !r.level) return null;
    const lift = (x) => (x.kind === 'Type' ? levelSucc(x.level) : x.level);
    return sortText('Sort', { k: 'app', f: { k: 'id', v: 'max' }, args: [lift(b), lift(r)] });
  }

  /**
   * Bound names, binder relation and range of a binder list, ignoring type annotations:
   * `y : ℝ in (0:ℝ)..s` and `y in (0 : ℝ)..s` → { names: [y], op: 'in', range: '(0:ℝ)..s' }.
   */
  function binderParts(b) {
    let t = (b || '').replace(/\s+/g, ' ').trim();
    let op = null;
    let range = null;
    const rel = t.match(/\s(in|∈|∉|<|≤|>|≥|≠|⊆)\s/);
    if (rel) {
      op = rel[1];
      range = t.slice(rel.index + rel[0].length).trim();
      t = t.slice(0, rel.index).trim();
    }
    let names = [];
    const groups = [...t.matchAll(/[({⦃[]\s*([^(){}⦃⦄[\]:]+?)\s*:/g)];
    if (groups.length) groups.forEach(g => names.push(...g[1].trim().split(/\s+/)));
    else names = t.split(':')[0].trim().split(/\s+/);
    return { names: names.filter(Boolean), op, range };
  }

  /** Substitute variables (Map name → node) into `n`. */
  function substTerm(n, sub) {
    if (!n) return n;
    if (n.k === 'app' && n.f.k === 'id' && sub.has(n.f.v)) {
      // `f x` with `f := fun x => b` becomes `b[x := …]`, as Lean's instantiation beta-reduces.
      const fn = tCore(sub.get(n.f.v));
      if (fn && fn.k === 'bind' && (fn.head === 'fun' || fn.head === 'λ')) {
        const params = boundNamesOf(fn.binders);
        const args = n.args.map(a => substTerm(a, sub));
        if (params.length && args.length >= params.length) {
          const body = substTerm(fn.body, new Map(params.map((p, i) => [p, args[i]])));
          const rest = args.slice(params.length);
          return rest.length ? { k: 'app', f: Object.assign({}, body, { paren: true }), args: rest } : body;
        }
      }
    }
    if (n.k === 'id') {
      if (sub.has(n.v)) return sub.get(n.v);
      const dot = n.v.indexOf('.');
      if (dot > 0 && sub.has(n.v.slice(0, dot))) return { k: 'proj', e: sub.get(n.v.slice(0, dot)), f: n.v.slice(dot + 1) };
      return n;
    }
    if (n.k === 'raw' || n.k === 'bind') {
      let text = n.k === 'raw' ? n.v : n.binders;
      sub.forEach((v, name) => { text = replaceWord(text, name, showTerm(v, 1025)); });
      const m = n.k === 'raw' ? Object.assign({}, n, { v: text }) : Object.assign({}, n, { binders: text });
      return n.k === 'bind' ? Object.assign(m, { body: substTerm(n.body, sub) }, n.idx ? { idx: substTerm(n.idx, sub) } : {}) : m;
    }
    const m = tWithChildren(n, tChildren(n).map(c => substTerm(c, sub)));
    return n.k === 'asc' ? Object.assign(m, { ty: substTerm(n.ty, sub) }) : m;
  }

  function freeNames(n, out = new Set()) {
    if (!n) return out;
    if (n.k === 'id') out.add(n.v.split('.')[0]);
    if (n.k === 'raw') namesIn(n.v).forEach(x => out.add(x));
    if (n.k === 'bind') namesIn(n.binders).forEach(x => out.add(x));
    tChildren(n).forEach(c => freeNames(c, out));
    return out;
  }

  function boundNamesOf(binders) {
    const names = [];
    const groups = binders.match(/[({⦃[]\s*[^(){}⦃⦄[\]:]+?\s*:/g);
    if (groups) groups.forEach(g => names.push(...g.replace(/^[({⦃[]\s*/, '').replace(/\s*:$/, '').split(/\s+/)));
    else names.push(...binders.split(/\s*(?::|∈|∉|<|≤|>|≥|≠|⊆|\bin\b)/)[0].trim().split(/\s+/));
    return names.filter(Boolean);
  }

  /**
   * Rewrite `tree` with `lhs = rhs` like `rw`: the first instance in pre-order fixes the
   * variables, then every equal instance (or only the `nth`) is replaced. Subterms that
   * mention variables bound by `∀`/`∃`/`fun` are skipped, as Lean's `rw` can't rewrite there.
   * Returns the new tree, or null if there is no instance.
   */
  function rewriteTerm(tree, lhs, rhs, vars, nth = 0) {
    const mentions = (n, bound) => bound.size > 0 && [...freeNames(n)].some(x => bound.has(x));
    const inner = (n, bound) => (n.k === 'bind' ? new Set([...bound, ...boundNamesOf(n.binders)]) : bound);
    let found = null;
    const find = (n, bound) => {
      if (found || !n) return;
      if (!mentions(n, bound)) {
        const sub = new Map();
        if (matchTerm(lhs, n, vars, sub)) { found = sub; return; }
      }
      tChildren(n).forEach(c => find(c, inner(n, bound)));
    };
    find(tree, new Set());
    if (!found) return null;
    // Every variable of the right side must be fixed by the match.
    if ([...freeNames(rhs)].some(x => vars.has(x) && !found.has(x))) return null;
    const inst = substTerm(lhs, found);
    const out = substTerm(rhs, found);
    let count = 0;
    let replaced = 0;
    const rep = (n, bound) => {
      if (!mentions(n, bound) && sameTerm(inst, n)) {
        count++;
        if (!nth || count === nth) { replaced++; return out; }
        return n;
      }
      return tWithChildren(n, tChildren(n).map(c => rep(c, inner(n, bound))));
    };
    const result = rep(tree, new Set());
    return replaced ? result : null;
  }

  /**
   * Binders and conclusion of a type or Loogle signature:
   * `{a b : α} (h : a ≤ b) : Set.uIcc a b = Set.Icc a b`, `∀ n, f n = n + 1`, `0 ≤ a → |a| = a`.
   * Premises `A →` count as unnamed explicit binders.
   */
  // Shared (memoized) result: callers must not change it.
  const peelSignature = memoized((type) => peelSignatureOf(type), 2000);

  function peelSignatureOf(type) {
    let t = (type || '').replace(/\s+/g, ' ').trim();
    if (/^:(?!=)/.test(t)) t = t.slice(1).trim(); // no parameters: `: T`
    const binders = [];
    let i = 0;
    while (i < t.length && '({[⦃'.includes(t[i])) {
      const close = matchClose(t, i);
      if (close === -1) break;
      const g = t.slice(i + 1, close);
      // The binder's own ` : ` (not one inside `[(i : ι) → AddCommMonoid (s i)]`).
      const tc = topColon(g);
      const c = tc !== -1 && g[tc - 1] === ' ' && g[tc + 1] === ' ' ? tc - 1 : -1;
      // A default value (`(hq : P := by simp)`) isn't part of the type.
      const dflt = c === -1 ? -1 : g.indexOf(' := ', c);
      if (c !== -1) binders.push({ names: g.slice(0, c).trim().split(/\s+/), type: g.slice(c + 3, dflt === -1 ? g.length : dflt).trim(), explicit: t[i] === '(', bi: t[i] });
      else binders.push({ names: [], type: g.trim(), explicit: false, bi: t[i] });
      i = close + 1;
      while (t[i] === ' ') i++;
    }
    if (i > 0) {
      if (t[i] === ':' && t[i + 1] !== '=') t = t.slice(i + 1).trim();
      else { binders.length = 0; } // not a signature: just a parenthesised type
    }
    for (let guard = 0; guard < 30; guard++) {
      while (t.startsWith('(') && matchClose(t, 0) === t.length - 1) t = t.slice(1, -1).trim();
      if (/^(∀|Π)/.test(t)) {
        const comma = topLevelIndexOf(t, ',');
        if (comma === -1) break;
        const seg = t.slice(1, comma).trim();
        if ('({[⦃'.includes(seg[0])) {
          let j = 0;
          while (j < seg.length) {
            while (seg[j] === ' ') j++;
            if (!'({[⦃'.includes(seg[j])) break;
            const close = matchClose(seg, j);
            if (close === -1) break;
            const g = seg.slice(j + 1, close);
            const c = g.indexOf(':');
            binders.push({ names: (c === -1 ? g : g.slice(0, c)).trim().split(/\s+/), type: c === -1 ? '' : g.slice(c + 1).trim(), explicit: seg[j] === '(', bi: seg[j] });
            j = close + 1;
          }
        } else {
          const pm = seg.match(/^([\w'Ͱ-Ͽ₀-ₜ\s]+?)\s*(∈|∉|<|≤|>|≥|≠|⊆)\s*(.+)$/);
          if (pm) {
            const names = pm[1].trim().split(/\s+/);
            binders.push({ names, type: '', explicit: true, bi: '(' });
            names.forEach(v => binders.push({ names: [], type: `${v} ${pm[2]} ${pm[3]}`, explicit: true, bi: '(' }));
          } else {
            const c = seg.indexOf(':');
            binders.push({ names: (c === -1 ? seg : seg.slice(0, c)).trim().split(/\s+/), type: c === -1 ? '' : seg.slice(c + 1).trim(), explicit: true, bi: '(' });
          }
        }
        t = t.slice(comma + 1).trim();
        continue;
      }
      // A dependent arrow `(a : α) → β a` / `{a : α} → …` / `[C] → …`: a binder.
      if ('({[⦃'.includes(t[0])) {
        const close = matchClose(t, 0);
        if (close !== -1 && /^\s*→\s/.test(t.slice(close + 1))) {
          const g = t.slice(1, close);
          const c = g.indexOf(' : ');
          // Only names before ` : ` (not `(⨂[R] i : ι, s i) → …`, a type in parentheses).
          const names = c === -1 ? [] : g.slice(0, c).trim().split(/\s+/);
          const binderNames = names.length && names.every(x => T_START.test(Array.from(x)[0]) && Array.from(x).every(ch => T_CONT.test(ch)));
          if ((c !== -1 && binderNames && t[0] !== '[') || t[0] === '[') {
            binders.push(c === -1 ? { names: [], type: g.trim(), explicit: false, bi: '[' }
              : { names: g.slice(0, c).trim().split(/\s+/), type: g.slice(c + 3).trim(), explicit: t[0] === '(', bi: t[0] });
            t = t.slice(close + 1).replace(/^\s*→\s*/, '');
            continue;
          }
        }
      }
      // A premise `A → B` (plain arrow at top level).
      let depth = 0, cut = -1;
      for (let k = 0; k < t.length; k++) {
        const ch = t[k];
        if (OPENERS[ch]) depth++;
        else if (CLOSERS.has(ch)) depth = Math.max(0, depth - 1);
        else if (depth === 0 && ch === '→' && t[k + 1] === ' ') { cut = k; break; }
        else if (depth === 0 && (ch === '=' || ch === '↔')) break; // an equation's sides may contain arrows
      }
      if (cut > 0) {
        binders.push({ names: [], type: t.slice(0, cut).trim(), explicit: true, bi: '(' });
        t = t.slice(cut + 1).trim();
        continue;
      }
      break;
    }
    return { binders, concl: t };
  }

  /**
   * `{ lhs, rhs, vars }` for a rewrite rule given its signature (constant or local), its
   * positional / named arguments, and direction. Hypothesis arguments fix variables through
   * their types (`h : 0 ≤ s` for `(h : a ≤ b)` gives `a := 0, b := s`).
   */
  /**
   * Instantiate a signature with an application's arguments. The signature's own variables are
   * renamed apart first, so arguments mentioning a local with the same name (`div_eq_iff hc`,
   * `hc : c ≠ 0`, while the lemma also has a `c`) can't be captured. Explicit arguments fill
   * explicit binders in order; hypothesis arguments fix variables through their types
   * (`h : 0 ≤ s` for `(h : a ≤ b)` gives `a := 0, b := s`); named arguments win.
   */
  function instantiateSignature(sig, positional, named, text, opts = {}) {
    const peeled = peelSignature(sig);
    // A constant's universe parameters (written `?u` by `universeParams`) are solved like
    // its other variables: `Type ?u` against `Type u_4` fixes `?u`.
    const univs = new Set();
    [peeled.concl, ...peeled.binders.map(b => b.type)].forEach(t => {
      for (const m of (t || '').matchAll(/\?[A-Za-z_\u0370-\u03FF][\w'\u0370-\u03FF\u2080-\u2089]*/g)) univs.add(m[0]);
    });
    const own = [...new Set(peeled.binders.flatMap(b => b.names))];
    const fresh = (n) => `__pv_${n}`;
    const ren = (str) => own.reduce((acc, n) => replaceWord(acc, n, fresh(n)), str || '');
    const binders = peeled.binders.map(b => ({ names: b.names.map(fresh), type: ren(b.type), explicit: b.explicit, bi: b.bi }));
    const vars = new Set([...binders.flatMap(b => b.names), ...[...univs].filter(u => !own.includes(u.slice(1)))]);
    const allSlots = binders.filter(b => b.explicit).flatMap(b => (b.names.length ? b.names : [null]).map(n => ({ name: n, type: b.type, binder: b })));
    // A named argument `(h := …)` fills its own parameter; positional ones fill the others.
    const namedKeys = new Set(Object.keys(named || {}).map(fresh));
    let slots = allSlots.filter(sl => !(sl.name && namedKeys.has(sl.name)));
    const sub = new Map();
    // Keep what a match fixed, except values with unknowns (`?a`, from an argument's own
    // unsolved type): those tell nothing and would block later arguments.
    const absorb = (extended) => extended.forEach((v, key) => {
      if (!sub.has(key) && ![...freeNames(v)].some(x => x.startsWith('?'))) sub.set(key, v);
    });
    const unify = (slotType, argType) => {
      const slotT = slotType && parseTerm(slotType);
      const argT = argType && parseTerm(argType);
      if (!slotT || !argT) return;
      const extended = new Map(sub);
      if (matchTerm(slotT, argT, vars, extended)) absorb(extended);
    };
    if (opts.receiver) {
      // `h.foo args`: the receiver fills the first explicit parameter of its type's head.
      const head = typeHead(opts.receiver.type || '', null);
      const k = slots.findIndex(sl => sl.type && head && typeHead(sl.type, null) === head);
      const at = k === -1 ? 0 : k;
      const slot = slots[at];
      if (slot) {
        const node = parseTerm(opts.receiver.term);
        if (node && slot.name) sub.set(slot.name, node);
        unify(slot.type, opts.receiver.type);
        slots = slots.filter((_, i) => i !== at);
      }
    }
    positional.forEach((a, k) => {
      const slot = slots[k];
      if (!slot || a === '_' || a === '?_') return;
      const node = parseTerm(a);
      if (node && slot.name) sub.set(slot.name, node);
      const given = opts.argTypes && opts.argTypes[k];
      if (given && typeof given === 'object') {
        // `⟨h₁, h₂⟩` for a parameter `A ∧ B` (or `A ↔ B`): each component's type against its part.
        const parts = tupleParts(slot.type && parseTerm(slot.type), given.tuple.length);
        (parts || []).forEach((part, i) => {
          const argT = given.tuple[i] && parseTerm(given.tuple[i]);
          const extended = new Map(sub);
          if (argT && matchTerm(part, argT, vars, extended)) absorb(extended);
        });
        return;
      }
      const argType = given || (/^[^\s()]+$/.test(a) ? localType(a, text) : null);
      unify(slot.type, argType);
    });
    for (const [n, v] of Object.entries(named || {})) {
      const node = parseTerm(v);
      if (node && own.includes(n)) sub.set(fresh(n), node);
    }
    // Out-params Mathlib's instances fix when a ring hom is the identity:
    // `RingHomInvPair (RingHom.id R) ?σ'` (σ' = id) and `RingHomCompTriple` with an id factor.
    const valueOf = (a) => (a.k === 'id' && vars.has(a.v) ? sub.get(a.v) : a);
    const isIdHom = (v) => { const c = v && tCore(v); return Boolean(c) && c.k === 'app' && c.f.k === 'id' && c.f.v === 'RingHom.id' && c.args.length === 1; };
    const outParam = (o, v) => { if (o.k === 'id' && vars.has(o.v) && !sub.has(o.v) && v) sub.set(o.v, v); };
    for (const b of binders) {
      const c = b.type && b.type.includes('RingHom') ? tCore(parseTerm(b.type)) : null;
      if (!c || c.k !== 'app' || c.f.k !== 'id') continue;
      const cls = c.f.v.split('.').pop();
      if (cls === 'RingHomInvPair' && c.args.length === 2 && isIdHom(valueOf(c.args[0]))) outParam(c.args[1], valueOf(c.args[0]));
      if (cls === 'RingHomCompTriple' && c.args.length === 3) {
        const [x, y] = [valueOf(c.args[0]), valueOf(c.args[1])];
        if (isIdHom(x)) outParam(c.args[2], y); else if (isIdHom(y)) outParam(c.args[2], x);
      }
    }
    // …and from the instances in scope (`[RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]` fixes `?σ₁₃`), as
    // instance search finds them.
    if (opts.instances && opts.instances.length) {
      for (const b of binders) {
        const c = b.type && /RingHom(?:InvPair|CompTriple)/.test(b.type) ? tCore(parseTerm(b.type)) : null;
        if (!c || c.k !== 'app' || c.f.k !== 'id') continue;
        const cls = c.f.v.split('.').pop();
        const ins = cls === 'RingHomInvPair' ? 1 : cls === 'RingHomCompTriple' ? 2 : 0;
        const out = c.args[ins];
        if (!ins || c.args.length !== ins + 1 || !out || out.k !== 'id' || !vars.has(out.v) || sub.has(out.v)) continue;
        const given = c.args.slice(0, ins).map(valueOf);
        if (given.some(g => !g)) continue;
        for (const local of opts.instances) {
          const l = tCore(parseTerm(local));
          if (l && l.k === 'app' && l.f.k === 'id' && l.f.v.split('.').pop() === cls && l.args.length === ins + 1 &&
              given.every((g, k) => sameTerm(g, l.args[k]))) { sub.set(out.v, l.args[ins]); break; }
        }
      }
    }
    // `RingHom.id R : R →+* R`.
    const idTypes = new Map();
    for (const v of sub.values()) { const c = tCore(v); if (isIdHom(c)) idTypes.set(showTerm(c), `${showTerm(c.args[0], 26)} →+* ${showTerm(c.args[0], 26)}`); }
    if (idTypes.size) {
      for (const b of binders) for (const n of b.names) { const v = sub.get(n); if (v && idTypes.has(showTerm(tCore(v))) && b.type) unify(b.type, idTypes.get(showTerm(tCore(v)))); }
    }
    // A variable solved by a local: the local's type fixes the variables in the binder's
    // type (`σ₁₂ := σ₁₂` with `σ₁₂ : R →+* R₂` gives `R`, `R₂`), as Lean unifies types.
    if (opts.valueTypes) {
      for (let pass = 0; pass < 3; pass++) {
        const before = sub.size;
        for (const b of binders) {
          for (const n of b.names) {
            const v = sub.get(n);
            const vt = v && tCore(v).k === 'id' ? opts.valueTypes.get(tCore(v).v) : null;
            if (vt && b.type) unify(b.type, vt);
          }
        }
        if (sub.size === before) break;
      }
    }
    return {
      concl: ren(peeled.concl), vars, sub, own, fresh, binders, slots: allSlots, remaining: slots.slice(positional.length),
      // Arguments beyond the parameters (`hs hx` with `hs : s ⊆ t`), with their types.
      extra: positional.slice(slots.length).map((a, i) => ({ arg: a, type: opts.argTypes ? opts.argTypes[slots.length + i] : null }))
    };
  }

  // Bundled functions written as structures (not arrows): what applying one to a point gives,
  // from the structure's arguments (`AlgebraNorm K L` is a function `L → ℝ`).
  const FUN_LIKE = {
    AlgebraNorm: (a) => a.length === 2 && 'ℝ', RingNorm: (a) => a.length === 1 && 'ℝ', RingSeminorm: (a) => a.length === 1 && 'ℝ',
    MulRingNorm: (a) => a.length === 1 && 'ℝ', MulRingSeminorm: (a) => a.length === 1 && 'ℝ', Seminorm: (a) => a.length === 2 && 'ℝ',
    AddGroupNorm: (a) => a.length === 1 && 'ℝ', AddGroupSeminorm: (a) => a.length === 1 && 'ℝ', GroupNorm: (a) => a.length === 1 && 'ℝ',
    GroupSeminorm: (a) => a.length === 1 && 'ℝ', NonarchAddGroupNorm: (a) => a.length === 1 && 'ℝ',
    AbsoluteValue: (a) => a.length === 2 && showTerm(a[1], 1025)
  };
  Object.setPrototypeOf(FUN_LIKE, null);

  function funLikeCodomain(t) {
    t = tCore(t);
    if (!t || t.k !== 'app' || t.f.k !== 'id') return null;
    const make = FUN_LIKE[t.f.v.replace(/^.*\./, '')];
    const cod = make && make(t.args);
    return cod ? parseTerm(cod) : null;
  }

  /** Expected types of the `n` components of `⟨…⟩` for type `t`: `A ∧ B ∧ C`, `A ↔ B`; or null. */
  function tupleParts(t, n) {
    t = tCore(t);
    if (!t || n < 2) return null;
    if (n === 2 && t.k === 'bin' && t.op === '↔') {
      return [{ k: 'bin', op: '→', l: t.l, r: t.r }, { k: 'bin', op: '→', l: t.r, r: t.l }];
    }
    const parts = [];
    for (let i = 0; i < n - 1; i++) {
      t = tCore(t);
      if (!t || t.k !== 'bin' || t.op !== '∧') return null;
      parts.push(t.l);
      t = t.r;
    }
    parts.push(t);
    return parts;
  }

  /**
   * Lean prints elaborated terms: type ascriptions `(0 : ℝ)` are gone (`0`), and a local
   * ascribed another type than its own is coerced (`(n : ℝ)` with `n : ℕ` is `↑n`; needs `text`).
   */
  function stripAscriptions(n, text) {
    if (!n) return n;
    if (n.k === 'proj' && n.e.k === 'asc' && tCore(n.e).k === 'num') return n; // `(0 : ℂ).im`
    if (n.k === 'asc') {
      const inner = stripAscriptions(n.e, text);
      if (text && n.e.k === 'id' && LOCAL_NAME.test(n.e.v)) {
        const own = parseTerm(localType(n.e.v, text) || '');
        if (own && !sameTerm(own, n.ty)) return { k: 'pre', op: '↑', e: inner };
      }
      return inner;
    }
    const kids = tChildren(n);
    return kids.length ? tWithChildren(n, kids.map(k => stripAscriptions(k, text))) : n;
  }

  /**
   * What an application leaves of a signature, as Lean elaborates it: implicit parameters up to
   * the first unfilled explicit one are instantiated (solved from the arguments' types, or left
   * as metavariables), instance parameters are synthesized (dropped here), and the remaining
   * parameters stay in the type. Returns { lead, rest, concl } (ASTs): `lead` are variables
   * nothing determined (Lean shows them as `?x`), `rest` the parameters from the first unfilled
   * explicit one on, `concl` the conclusion. `opts.receiver = { term, type, binders }` fills the
   * parameter of generalized field notation; `binders` are the receiver's own unsolved variables.
   */
  function residualParts(sig, positional, named, text, opts = {}) {
    const inst = instantiateSignature(sig, positional, named, text, opts);
    // A type with its variables substituted; notation we can't parse is kept as text. Binders
    // print as Lean prints them (`⨂[R] (i : ι), s i`), their types from the signature's.
    const sigTypes = new Map();
    inst.binders.forEach(b => b.names.forEach(nm => sigTypes.set(nm, b.type)));
    const typeOfName = (nm) => sigTypes.get(nm) || null;
    const subst = (s) => {
      if (!s || s === '_') return null;
      const n = parseTerm(s);
      return substTerm(n ? coerceApps(annotateBinders(n, typeOfName), typeOfName) : { k: 'raw', v: s, loose: true }, inst.sub);
    };
    // A bundled map (`f : M →+ N`) applied to a point is coerced to a function: Lean prints
    // `(liftAux φ) (a + b)` when the map is itself an application.
    inst.binders.forEach(b => {
      if (!isBundledType(parseTerm(b.type || ''))) return;
      b.names.forEach(nm => {
        const v = inst.sub.get(nm);
        if (v && tCore(v).k === 'app') inst.sub.set(nm, Object.assign({}, v, { coeFn: true }));
      });
    });
    let concl = subst(inst.concl);
    if (!concl) return null;
    // More arguments than parameters: only a few types are functions in disguise, applied one
    // argument at a time (`lift φ x`: `lift` is an equivalence, `lift φ` a linear map).
    for (const extra of inst.extra) {
      const c = tCore(concl);
      const argT = typeof extra.type === 'string' ? tCore(parseTerm(extra.type)) : null;
      if (c && c.k === 'bin' && (c.op === '⊆' || c.op === '⊂')) {
        // `hs : s ⊆ t` applied to `hx : x ∈ s` is `x ∈ t`.
        if (!argT || argT.k !== 'bin' || argT.op !== '∈' || !sameTerm(argT.r, c.l)) return null;
        concl = { k: 'bin', op: '∈', l: argT.l, r: c.r };
      } else {
        // A bundled map (`e : A ≃ B`, `f : M →+* N`, `‖·‖ : AlgebraNorm K L`) applied to a point
        // lands in its codomain, through the coercion to a function.
        const fun = funLikeCodomain(c);
        // `tprod R : (Π i, s i) →ₘₗ[R] ⨂[R] i, s i` applied to `f`: `f`'s type fixes `s`.
        let mapped = null;
        const dc = !fun && c ? bundledDomCod(c) : null;
        if (dc) {
          const extended = new Map();
          if (argT && matchTerm(dc.dom, argT, inst.vars, extended)) extended.forEach((v, key) => { if (!inst.sub.has(key)) inst.sub.set(key, v); });
          // What the point fixed can fix more, through the locals' types (`s : ι → Type*` gives `ι`).
          if (opts.valueTypes) {
            for (const b of inst.binders) {
              for (const nm of b.names) {
                const v = inst.sub.get(nm);
                const vt = v && tCore(v).k === 'id' ? opts.valueTypes.get(tCore(v).v) : null;
                const more = new Map(inst.sub);
                if (vt && b.type && matchTerm(parseTerm(b.type), parseTerm(vt), inst.vars, more)) {
                  more.forEach((x, key) => { if (!inst.sub.has(key)) { inst.sub.set(key, x); extended.set(key, x); } });
                }
              }
            }
          }
          mapped = substTerm(dc.cod, extended);
        }
        const cod = fun || mapped ? null : codomainOf(showTerm(concl));
        const codT = fun || mapped || (cod && parseTerm(cod));
        if (!codT) return null;
        concl = codT;
      }
    }
    // The last argument goes through the coercion to a function: `(tprod R) f`.
    const applied = inst.extra.length ? tCore(subst(inst.concl)) : null;
    if (applied && !['⊆', '⊂'].includes(applied.op) && opts.onCoerce) opts.onCoerce(positional.length - 1);
    const lead = [];
    const rest = [];
    const recv = (opts.receiver && opts.receiver.binders) || [];
    recv.forEach(x => lead.push({ name: x.name, type: x.type }));
    const remaining = new Set(inst.remaining);
    let open = false; // past the first unfilled explicit parameter
    for (const b of inst.binders) {
      if (b.explicit) {
        for (const sl of inst.slots) {
          if (sl.binder !== b || !remaining.has(sl)) continue;
          open = true;
          rest.push({ name: sl.name, type: subst(sl.type), bi: '(' });
        }
      } else if (b.bi !== '[') {
        for (const n of b.names) {
          if (inst.sub.has(n)) continue;
          (open ? rest : lead).push({ name: n, type: subst(b.type), bi: '{' });
        }
      }
    }
    if (rest.some(x => x.bi === '(' && !x.type && !x.name)) return null;
    // Back from the internal `__pv_x` names, avoiding names already free in the result.
    const taken = new Set(recv.map(x => x.name));
    [concl, ...lead.map(x => x.type), ...rest.map(x => x.type)].filter(Boolean)
      .forEach(n => freeNames(n).forEach(x => { if (!x.startsWith('__pv_')) taken.add(x); }));
    const back = new Map();
    for (const x of [...lead, ...rest]) {
      if (!x.name || !x.name.startsWith('__pv_') || back.has(x.name)) continue;
      let nm = x.name.slice(5);
      while (taken.has(nm)) nm += "'";
      taken.add(nm);
      back.set(x.name, { k: 'id', v: nm });
    }
    const fix = (n) => (n ? substTerm(n, back) : n);
    const rename = (nm) => (nm && back.has(nm) ? back.get(nm).v : nm);
    const out = {
      lead: lead.map(x => ({ name: rename(x.name), type: fix(x.type) })),
      rest: rest.map(x => ({ name: rename(x.name), type: fix(x.type), bi: x.bi })),
      concl: fix(concl)
    };
    // A parameter whose argument we couldn't read would dangle in the result.
    const dangling = [out.concl, ...out.rest.map(x => x.type)].filter(Boolean)
      .some(n => [...freeNames(n)].some(x => x.startsWith('__pv_')));
    return dangling ? null : out;
  }

  const BINDER_PRED_OPS = new Set(['∈', '∉', '<', '≤', '>', '≥', '≠', '⊆', '⊂']);

  /** `rest` and `concl` of `residualParts` as a type: `(x : T) → …` / `T → …` / `∀ {x : T}, …`. */
  // Type constructors: a function type into one of these is data, printed `(a : α) → β a`.
  const DATA_HEADS = new Set(['Set', 'Finset', 'List', 'Multiset', 'Option', 'Fin', 'Matrix', 'Polynomial', 'MvPolynomial',
    'PiTensorProduct', 'TensorProduct', 'MultilinearMap', 'LinearMap', 'LinearEquiv', 'Submodule', 'Subgroup', 'AddSubgroup',
    'Subring', 'Subalgebra', 'Ideal', 'Equiv', 'Prod', 'Sum', 'Sigma', 'Subtype', 'Quotient', 'Module.End', 'Finsupp',
    'ℕ', 'ℤ', 'ℚ', 'ℝ', 'ℂ', 'Nat', 'Int', 'Rat', 'Real', 'Complex', 'Type', 'Sort', 'Bool', 'Unit', 'ENNReal', 'NNReal', 'EReal']);

  /** Is `n` a type whose values are data (not proofs)? Unknown shapes count as propositions. */
  function isDataType(n) {
    n = tCore(n);
    if (!n) return false;
    if (n.k === 'bin') return T_MAP_OPS.includes(n.op) || ['×', '≃', '↪'].includes(n.op) || (n.op === '→' && isDataType(n.r));
    if (n.k === 'bind') return ['⨂[_]', '⨁'].includes(n.head) || (n.arrow && isDataType(n.body));
    const head = n.k === 'app' ? tCore(n.f) : n;
    if (!head || head.k !== 'id') return false;
    if (DATA_HEADS.has(head.v)) return true;
    // A type family `s a`, `β i`, `M i`, `?β a` (predicates are `p x`, `P x`, `q x`, `r a b`).
    return n.k === 'app' && /^\??[A-Za-zα-ωΑ-Ω][\d'\u2080-\u2089]*$/.test(head.v) && !/^[pqrPQ]/.test(head.v.replace(/^\?/, ''));
  }

  function piOf(rest, concl) {
    let body = concl;
    for (let i = rest.length - 1; i >= 0; i--) {
      const x = rest[i];
      const later = [body, ...rest.slice(i + 1).map(r => r.type)].filter(Boolean);
      const dependent = Boolean(x.name) && later.some(n => freeNames(n).has(x.name));
      const ty = x.type ? showTerm(x.type) : null;
      // `∀ x, x ∈ s → p x` is written `∀ x ∈ s, p x` (Mathlib's binder predicates).
      const pred = body && body.k === 'bin' && body.op === '→' && body.l.k === 'bin' && BINDER_PRED_OPS.has(body.l.op) &&
        body.l.l.k === 'id' && body.l.l.v === x.name;
      // A function type whose values are data prints as `(a : α) → β a`, a proposition as `∀ (a : α), …`.
      const data = ty && isDataType(body);
      if (x.bi === '{') {
        body = data ? { k: 'bind', head: 'Π', arrow: true, binders: `{${x.name} : ${ty}}`, sep: '→', body }
          : { k: 'bind', head: '∀', binders: ty ? `{${x.name} : ${ty}}` : `{${x.name}}`, sep: ',', body };
      } else if (pred && !x.type) body = { k: 'bind', head: '∀', binders: `${x.name} ${body.l.op} ${showTerm(body.l.r, 51)}`, sep: ',', body: body.r };
      else if (dependent && data) body = group({ k: 'bind', head: 'Π', arrow: true, binders: `(${x.name} : ${ty})`, sep: '→', body });
      else if (dependent || !x.type) body = group({ k: 'bind', head: '∀', binders: ty ? `(${x.name} : ${ty})` : (x.name || '_'), sep: ',', body });
      else body = { k: 'bin', op: '→', l: x.type, r: body };
    }
    return body;
  }

  const BUNDLED_HEADS = new Set(Object.values(ARROW_HEADS).filter(Boolean).map(h => h.split('.').pop()));

  /** Is `t` the type of a bundled map, which applies to points through a coercion? */
  function isBundledType(t) {
    t = tCore(t);
    if (!t) return false;
    if (t.k === 'bin') return (T_MAP_OPS.includes(t.op) && !/^[⊗∘≪⨂]/.test(t.op)) || t.op === '≃' || t.op === '↪';
    const head = t.k === 'app' ? tCore(t.f) : t;
    return Boolean(head) && head.k === 'id' && (BUNDLED_HEADS.has(head.v.split('.').pop()) || Object.prototype.hasOwnProperty.call(FUN_LIKE, head.v.split('.').pop()));
  }

  /**
   * Domain and codomain of a bundled map type: `A →ₗ[R] B`, and the structures written as
   * applications (`LinearMap σ M M₂`, `MultilinearMap R M N` on `(i : ι) → M i`); or null.
   */
  function bundledDomCod(t) {
    t = tCore(t);
    if (!t) return null;
    if (t.k === 'bin') return isBundledType(t) ? { dom: t.l, cod: t.r } : null;
    if (t.k !== 'app' || t.f.k !== 'id' || !isBundledType(t) || t.args.length < 2) return null;
    const head = t.f.v.split('.').pop();
    const [dom, cod] = t.args.slice(-2);
    if (head === 'MultilinearMap') {
      return { dom: { k: 'bind', head: 'Π', binders: 'i', sep: ',', body: { k: 'app', f: dom, args: [{ k: 'id', v: 'i' }] } }, cod };
    }
    return { dom, cod };
  }

  /** `∀ (a : M), ∀ (b : M), P` prints as `∀ (a b : M), P` (Lean groups binders of one type). */
  function group(n) {
    const inner = n.body;
    const m = n.binders.match(/^\(([^():]+) : ([\s\S]+)\)$/);
    if (!m || !inner || inner.k !== 'bind' || inner.head !== n.head || Boolean(inner.arrow) !== Boolean(n.arrow)) return n;
    const im = inner.binders.match(/^\(([^():]+) : ([\s\S]+)\)$/);
    if (!im || im[2] !== m[2] || m[1].trim().split(/\s+/).some(x => namesIn(im[2]).includes(x))) return n;
    return Object.assign({}, inner, { binders: `(${m[1].trim()} ${im[1].trim()} : ${m[2]})` });
  }

  const leadBinderText = (lead) => lead.map(x => `{${x.name} : ${x.type ? showTerm(x.type) : '_'}}`).join(' ');

  /**
   * The residual of `residualParts` as a signature text that can be applied further:
   * `{b : α} : 0 < b → 0 < x * b` for `mul_pos hx`. Null if it can't be worked out.
   */
  function residualSignature(sig, positional, named, text, opts = {}) {
    const r = residualParts(sig, positional, named, text, opts);
    return r ? `${leadBinderText(r.lead)} : ${showTerm(piOf(r.rest, r.concl))}`.trim() : null;
  }

  /**
   * Type of an application from its head's signature, as Lean's hover shows it: explicit
   * arguments fill parameters in order, implicit ones are solved from the arguments' types,
   * unfilled parameters stay as arrows (`f 1 : ℕ → ℕ`), unknown variables show as `?x`.
   */
  function applyArgs(sig, positional, named, text, opts = {}) {
    const r = residualParts(sig, positional, named, text, opts);
    if (!r) return null;
    const mv = new Map(r.lead.map(x => [x.name, { k: 'id', v: `?${x.name}` }]));
    const out = substTerm(piOf(r.rest, r.concl), mv);
    return showTerm(opts.keepAscriptions ? out : stripAscriptions(out, text));
  }

  /** Does `t` start with binder groups followed by ` : ` (a signature, not a plain type)? */
  function isSignature(t) {
    let i = 0;
    const s = (t || '').trim();
    if (/^:(?!=)/.test(s)) return true;
    while (i < s.length && '({[⦃'.includes(s[i])) {
      const close = matchClose(s, i);
      if (close === -1) return false;
      i = close + 1;
      while (s[i] === ' ') i++;
    }
    return i > 0 && s[i] === ':' && s[i + 1] !== '=';
  }

  /**
   * A declaration's signature as Lean's hover prints it, `name.{u} binders : type`: no
   * declaration keyword, no auto-generated instance names (`[inst : Ring R]` → `[Ring R]`),
   * the universe parameters named in the statement after the name.
   */
  function leanSignature(name, sig, known = null) {
    let t = (sig || '').replace(/\s+/g, ' ').trim();
    if (!t) return name;
    t = t.replace(/\[inst(?:_\d+|✝\d*)? : /g, '[');
    t = leanBinders(t, known);
    const univs = [];
    const add = (u) => { if (/^[a-zA-Z_][\w'\u2080-\u2089]*$/.test(u) && !['max', 'imax', '_'].includes(u) && !univs.includes(u)) univs.push(u); };
    for (const m of t.matchAll(/(?<![\w'.])(?:Type|Sort)\s+(\([^()]*\)|[a-zA-Z_][\w'\u2080-\u2089]*)/g)) {
      (m[1].startsWith('(') ? m[1].slice(1, -1).split(/[\s+]+/) : [m[1]]).forEach(add);
    }
    const head = univs.length ? `${name}.{${univs.join(', ')}}` : name;
    // Binders only (`structure Foo (α : Type*) where`): no type to show.
    let i = 0;
    while (i < t.length && '({[⦃'.includes(t[i])) {
      const close = matchClose(t, i);
      if (close === -1) break;
      i = close + 1;
      while (t[i] === ' ') i++;
    }
    return isSignature(t) || (i > 0 && i >= t.length) ? `${head} ${t}` : `${head} : ${t}`;
  }

  /**
   * A signature's binders and type with Lean's binder printing (`annotateBinders`), the types
   * of names read from its own binders: `[∀ i, AddCommMonoid (s i)]` is
   * `[(i : ι) → AddCommMonoid (s i)]` given `{s : ι → Type u_8}`.
   */
  // The same binder text with the same types for its names prints the same: section variables
  // come back in every declaration's signature.
  const annotateCache = new Map();

  function annotateCached(text, typeOfName, instance) {
    const names = (text.match(/(?<![\w'.\u0370-\u03FF\u2080-\u209C])[A-Za-z_\u0370-\u03FF\u1F00-\u1FFF][\w'.\u0370-\u03FF\u1F00-\u1FFF\u2080-\u209C]*/g) || [])
      .flatMap(n => (n.includes('.') ? [n, n.split('.')[0]] : [n])); // (`p.Prime` depends on `p`'s type)
    const key = `${instance ? 1 : 0}\u0000${text}\u0000${[...new Set(names)].map(n => `${n}:${typeOfName(n) || ''}`).join('\u0001')}`;
    if (annotateCache.has(key)) return annotateCache.get(key);
    const out = annotateTextNow(text, typeOfName, instance);
    if (annotateCache.size > 3000) annotateCache.clear();
    annotateCache.set(key, out);
    return out;
  }

  function leanBinders(sig, known = null) {
    const out = [];
    const types = new Map();
    const typeOfName = (nm) => types.get(nm) || (known && known(nm)) || null;
    const annotateText = annotateCached;
    let t = sig.trim();
    let i = 0;
    while (i < t.length && '({[⦃'.includes(t[i])) {
      const close = matchClose(t, i);
      if (close === -1) return sig;
      const g = t.slice(i + 1, close);
      const c = topColon(g);
      if (c === -1) {
        out.push(t[i] === '[' ? `[${annotateText(g.trim(), typeOfName, true)}]` : t.slice(i, close + 1));
      } else {
        const names = g.slice(0, c).trim();
        const ty = annotateText(g.slice(c + 1).trim(), typeOfName, t[i] === '[');
        names.split(/\s+/).forEach(nm => types.set(nm, g.slice(c + 1).trim()));
        out.push(`${t[i]}${names} : ${ty}${OPENERS[t[i]]}`);
      }
      i = close + 1;
      while (t[i] === ' ') i++;
    }
    const rest = t.slice(i);
    const colon = rest.match(/^:(?!=)\s*/);
    if (!colon) return [...mergeBinders(out), rest].filter(Boolean).join(' ');
    const hoisted = hoistBinders(out, annotateText(rest.slice(colon[0].length), typeOfName), typeOfName);
    return [...mergeBinders(hoisted.groups), `: ${hoisted.concl}`].join(' ');
  }

  /** The names a binder group `(a b : T)` / `[inst : C]` binds (none for `[C]`). */
  function groupNames(g) {
    const inner = g.slice(1, -1);
    const c = topColon(inner);
    return c === -1 ? [] : inner.slice(0, c).trim().split(/\s+/).filter(Boolean);
  }

  /** `(a : ℕ) {b : ℕ}` as its groups, or null unless it is only bracketed groups. */
  function bracketGroups(text) {
    const groups = [];
    let i = 0;
    const t = text.trim();
    while (i < t.length) {
      if (!'({[⦃'.includes(t[i])) return null;
      const close = matchClose(t, i);
      if (close === -1) return null;
      groups.push(t.slice(i, close + 1));
      i = close + 1;
      while (t[i] === ' ') i++;
    }
    return groups.length ? groups : null;
  }

  /** The element type of a set-like term (`s : Finset ℕ`, `S p` with `S … : Set α`), or null. */
  function memberType(range, typeOfName) {
    const n = tCore(parseTerm(range || ''));
    if (!n) return null;
    let ty = null;
    if (n.k === 'id') ty = typeOfName(n.v);
    else if (n.k === 'app' && tCore(n.f) && tCore(n.f).k === 'id') {
      const p = peelSignature(typeOfName(tCore(n.f).v) || '');
      const explicit = p.binders.filter(b => b.explicit).flatMap(b => b.names);
      const used = freeNames(parseTerm(p.concl) || { k: 'id', v: '' });
      if (explicit.length === n.args.length && !explicit.some(x => used.has(x))) ty = p.concl;
    }
    const m = ty && ty.replace(/^:\s*/, '').trim().match(/^(?:Set|Finset|List|Multiset)\s+([\s\S]+)$/);
    return m ? stripParens(m[1].trim()) : null;
  }

  /**
   * Lean's signature printer takes a type's leading named `∀` binders as parameters: `(s : Set ℕ)
   * : ∀ t : Set ℕ, t ⊆ s → P` prints `(s t : Set ℕ) : t ⊆ s → P` (with `mergeBinders`) and `∀ x ∈
   * s, P x` prints `(x : ℕ) : x ∈ s → P x`; a name already bound prints `n✝`. Binders whose
   * type isn't known stay in the type. { groups, concl }.
   */
  function hoistBinders(groups, concl, typeOfName) {
    const bound = new Set(groups.flatMap(groupNames));
    let body = concl;
    for (let guard = 0; guard < 20; guard++) {
      const n = parseTerm(body);
      if (!n || n.k !== 'bind' || !(n.head === '∀' || (n.head === 'Π' && n.arrow))) break;
      const parts = binderParts(n.binders);
      let add;
      let next = n.body;
      if (parts.op) {
        if (parts.names.length !== 1 || parts.op === 'in') break;
        const x = parts.names[0];
        const other = typeOfName(parts.range.trim());
        const ty = parts.op === '∈' || parts.op === '∉' ? memberType(parts.range, typeOfName)
          : (other && !/^[:({[⦃]/.test(other.trim()) && topColon(other) === -1 ? other.trim() : null);
        const guardTerm = ty && parseTerm(`${x} ${parts.op} ${parts.range}`);
        if (!guardTerm) break;
        add = [`(${x} : ${ty})`];
        next = { k: 'bin', op: '→', l: guardTerm, r: n.body };
      } else {
        add = bracketGroups(n.binders);
        if (!add || add.some(g => g[0] !== '[' && topColon(g.slice(1, -1)) === -1) || add.some(g => groupNames(g).includes('_'))) break;
      }
      let text = showTerm(next);
      // Names bound already print `n✝`, in their binder, later binders and the body.
      for (let k = 0; k < add.length; k++) {
        for (const nm of groupNames(add[k])) {
          if (!bound.has(nm)) { bound.add(nm); continue; }
          const dag = `${nm}✝`;
          add[k] = add[k].replace(new RegExp(`^(.)((?:[^:]*?\\s)?)${nm.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}(?=[\\s:])`), (m, o, pre) => `${o}${pre}${dag}`);
          for (let j = k + 1; j < add.length; j++) add[j] = replaceWord(add[j], nm, dag);
          text = replaceWord(text, nm, dag);
          bound.add(dag);
        }
      }
      groups = groups.concat(add);
      body = text;
    }
    return { groups, concl: body };
  }

  /** Consecutive binders of one kind and type print as one group, as Lean prints them: `(a b : ℕ)`. */
  function mergeBinders(groups) {
    const out = [];
    for (const g of groups) {
      const last = out[out.length - 1];
      const c = g[0] === '[' ? -1 : topColon(g.slice(1, -1));
      const lc = last && last[0] === g[0] ? topColon(last.slice(1, -1)) : -1;
      if (c !== -1 && lc !== -1 && !g.includes(' := ') && !last.includes(' := ')) {
        const type = g.slice(1, -1).slice(c + 1).trim();
        const names = groupNames(last);
        if (type === last.slice(1, -1).slice(lc + 1).trim() && !names.some(x => new RegExp(`(?<![\\w'.])${x.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}(?![\\w'])`).test(type))) {
          out[out.length - 1] = `${g[0]}${[...names, ...groupNames(g)].join(' ')} : ${type}${OPENERS[g[0]]}`;
          continue;
        }
      }
      out.push(g);
    }
    return out;
  }

  /** A signature or type as Lean prints the type of a term: `?x` for unsolved variables. */
  function displayType(sig, text = '', keepAscriptions = false) {
    if (!sig) return null;
    if (isSignature(sig)) return applyArgs(sig, [], {}, text, { keepAscriptions });
    const n = parseTerm(sig);
    return n ? showTerm(keepAscriptions ? n : stripAscriptions(n, text)) : sig.replace(/\s+/g, ' ').trim();
  }

  function ruleEquationFrom(sig, positional, named, rev, text) {
    const inst = instantiateSignature(sig, positional, named, text);
    const c = parseTerm(inst.concl);
    if (!c || c.k !== 'bin' || (c.op !== '=' && c.op !== '↔')) return null;
    let lhs = substTerm(c.l, inst.sub);
    let rhs = substTerm(c.r, inst.sub);
    if (rev) [lhs, rhs] = [rhs, lhs];
    return { lhs, rhs, vars: new Set([...inst.vars].filter(v => !inst.sub.has(v))) };
  }

  /**
   * Type of `head args…` from `head`'s signature: its conclusion with the arguments
   * substituted. Variables no argument determines keep their names and are reported.
   */
  function applicationTypeFrom(sig, positional, named, text) {
    const inst = instantiateSignature(sig, positional, named, text);
    const c = parseTerm(inst.concl);
    if (!c) return null;
    const out = substTerm(c, inst.sub);
    const unresolved = [...freeNames(out)].filter(x => inst.vars.has(x)).map(x => x.slice(5));
    const back = new Map(inst.own.map(n => [inst.fresh(n), { k: 'id', v: n }]));
    return { type: showTerm(substTerm(out, back)), unresolved };
  }

  /**
   * Type of `recv.field` from the field constant's signature: the receiver fills the first
   * explicit parameter whose type has the receiver's head (Lean's rule), matched as terms
   * so infix types work (`self : a ↔ b` against `P ↔ Q`). Returns the conclusion text.
   */
  function receiverResultType(sig, receiverType) {
    const inst = instantiateSignature(sig, [], {}, '');
    const peeled = peelSignature(sig);
    const recvT = parseTerm(receiverType);
    const head = typeHead(receiverType, null);
    if (!recvT || !head) return null;
    // The receiver's parameter: one whose type has the receiver's head, explicit first
    // (`Fact.out` takes it as the instance `[self : Fact p]`).
    const typed = peeled.binders.filter(b => b.type && typeHead(b.type, null) === head);
    const slot = typed.find(b => b.explicit) || typed[0];
    if (!slot) return null;
    // The parameter's type, with the signature's variables renamed apart like the conclusion.
    const slotT = parseTerm(inst.own.reduce((acc, n) => replaceWord(acc, n, inst.fresh(n)), slot.type));
    const sub = new Map(inst.sub);
    if (!slotT || !matchTerm(slotT, recvT, inst.vars, sub)) return null;
    sub.forEach((v, k) => inst.sub.set(k, v));
    const c = parseTerm(inst.concl);
    if (!c) return null;
    const back = new Map(inst.own.map(n => [inst.fresh(n), { k: 'id', v: n }]));
    return showTerm(substTerm(substTerm(c, inst.sub), back));
  }

  /**
   * The statement of a field in its place: `recv.field` for `recv : receiverType`, from the
   * field constant's signature. `Nat.even_add_one.mp` is `Even (n + 1) → ¬Even n`, where the
   * constant alone (`Iff.mp`) only says `a → b`. Parameters the receiver doesn't fix stay in
   * the type (`h.trans : b ≤ ?c → a ≤ ?c`). Null when it can't be worked out.
   */
  function fieldTypeOf(sig, receiverTerm, receiverType) {
    const head = typeHead(receiverType, null);
    if (!head) return null;
    try {
      const explicitSlot = peelSignature(sig).binders.some(b => b.explicit && b.type && typeHead(b.type, null) === head);
      // (A receiver that fills an instance or implicit parameter, as in `Fact.out`, leaves the conclusion.)
      return (explicitSlot
        ? applyArgs(sig, [], {}, '', { receiver: { term: receiverTerm, type: receiverType, binders: [] } })
        : receiverResultType(sig, receiverType)) || null;
    } catch (err) {
      return null;
    }
  }

  /**
   * A signature as Lean prints it (`Iff.mp.{u} {a b : Prop} (self : a ↔ b) : a → b`) without
   * its name: `{ binders, type }` (`binders` as written, `type` after the colon), or null.
   */
  function signatureParts(name, signature) {
    let body = String(signature || '').replace(/\s+/g, ' ').trim();
    if (name && body.startsWith(name)) body = body.slice(name.length);
    else body = body.replace(/^[^\s:({\[⦃]+/, ''); // a private name prints without its prefix
    body = body.replace(/^\.\{[^}]*\}/, '').trim();
    const colon = topColon(body);
    if (colon === -1) return null;
    return { body, binders: body.slice(0, colon).trim(), type: body.slice(colon + 1).trim() };
  }

  /**
   * A chain of fields in its place: `head.f₁.….fₙ` from the head's hover and each field
   * constant's signature. `head` is `{ name, type }` (a local) or `{ name, signature }` (a
   * constant, which must take no explicit argument); `fields` are `{ text, name, signature }`.
   * Returns `{ term, signature }`, e.g. `Nat.even_add_one.mp {n : ℕ} : Even (n + 1) → ¬Even n`.
   */
  function fieldChainInPlace(head, fields) {
    let term = head.name;
    let type = head.type || null;
    let binders = '';
    if (!type) {
      const parts = signatureParts(head.name, head.signature);
      if (!parts || peelSignature(parts.body).binders.some(b => b.explicit)) return null;
      binders = parts.binders;
      type = parts.type;
    }
    for (const field of fields) {
      const parts = signatureParts(field.name, field.signature);
      const next = parts && fieldTypeOf(parts.body, term, type);
      if (!next) return null;
      term = `${term}.${field.text}`;
      type = next;
    }
    return { term, signature: `${term}${binders ? ` ${binders}` : ''} : ${type}` };
  }

  /** Head, positional and named arguments of an application `f a (b := c) d`. */
  function appParts(term) {
    const t = (term || '').trim().replace(/^@/, '');
    const head = applicationHead(t);
    if (!head) return null;
    const positional = [];
    const named = Object.create(null);
    for (const a of splitApp(t).slice(1)) {
      const nm = a.match(/^\(\s*([^\s:()]+)\s*:=\s*([\s\S]+)\)$/);
      if (nm) named[nm[1]] = nm[2].trim();
      else positional.push(a);
    }
    return { head, positional, named };
  }

  const LOCAL_NAME = /^[\w'Ͱ-Ͽἀ-῿₀-ₜ]+$/;

  (typeof window !== 'undefined' ? window : self).LeanTerms = {
    hooks,
    OPENERS, CLOSERS, ARROW_HEADS, PREFIX_HEADS, INFIX_HEADS, NOTATION_HEADS, matchClose, topLevelIndexOf,
    topLevelArrow, codomainOf, typeHead, conclusionOf, applicationHead, IDENT_SPLIT, namesIn, topColon,
    stripParens, replaceWord, splitTop, USE_NOT_FN, useRegex, useOf, domainOf, domainSync, PROP_CLASSES,
    annotateBinders, annotateText, annotateTextNow, plainFunBinders, coerceApps, splitApp, T_START, T_CONT,
    T_OPS, T_BIN, T_MAP_OPS, SEMI_OF, LINEAR_OF, T_BINDER_HEADS, T_BODY_PREC, T_STOP_WORDS, T_UNMODELLED,
    T_OPENERS, T_CLOSERS, tokenizeTerm, T_MAP_START, T_MAP_BY_FIRST, tMapOp, tPeek, tNext, tIs, T_FAIL,
    tExpect, memoized, parseTerm, tRawUntil, tStartsArg, tBinder, tSpan, tPrefix, tPrefixBody, tPostfix,
    tArg, tExpr, arrowBinder, tPrec, showTerm, tCore, tIdEq, tRawEq, tChildren, tWithChildren, matchTerm,
    sameTerm, flatApp, universeParams, sortOf, levelSucc, levelPred, lvlNum, lvlOffset, lvlAdd, lvlArgs,
    lvlKind, lvlLeq, lvlSimp, lvlDec, lvlShow, isLevel, sortText, piSort, binderParts, substTerm, freeNames,
    boundNamesOf, rewriteTerm, peelSignature, peelSignatureOf, instantiateSignature, FUN_LIKE,
    funLikeCodomain, tupleParts, stripAscriptions, residualParts, BINDER_PRED_OPS, DATA_HEADS, isDataType,
    piOf, BUNDLED_HEADS, isBundledType, bundledDomCod, group, leadBinderText, residualSignature, applyArgs,
    isSignature, leanSignature, annotateCache, annotateCached, leanBinders, displayType, ruleEquationFrom,
    applicationTypeFrom, receiverResultType, fieldTypeOf, signatureParts, fieldChainInPlace, appParts, LOCAL_NAME
  };
})();
