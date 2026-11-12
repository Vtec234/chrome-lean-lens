/**
 * Receiver type inference for dot notation in GitHub Lean diffs.
 *
 * For `hl.nodup` we look for the binder of `hl` in the enclosing declaration,
 * e.g. `(hl : l.SortedLT)`, work out the head constant of that type
 * (`List.SortedLT`, using `l : List α`), and resolve the field as
 * `List.SortedLT.nodup`, which is what Lean's generalized field notation does.
 *
 * Purely textual: no elaboration, so it only handles explicit binders,
 * `have`/`let`-style annotations, and simple type heads.
 */

(function () {
  const OPENERS = { '(': ')', '{': '}', '⦃': '⦄', '[': ']', '⟨': '⟩' };
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

  const DECL_START = /^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|public|noncomputable|scoped|partial|nonrec|unsafe|meta)\s+)*(?:theorem|lemma|def|instance|example|abbrev|opaque)\b/;

  const NAME_CHARS = "[^\\s:()\\[\\]{}⦃⦄⟨⟩,]+";
  const BINDER_NAMES = new RegExp(`^\\s*(${NAME_CHARS}(?:\\s+${NAME_CHARS})*)\\s*:(?!=)`);
  const BINDER_KW = new RegExp(`(?:\\bfun|λ|∀|∃!?|Π|∑'?|∏'?|⋃|⋂|⨆|⨅|∫|∮)\\s+(${NAME_CHARS}(?:\\s+${NAME_CHARS})*)\\s*:(?!=)`, 'g');
  // `have h : T`, `have h (x) : T`, `by_cases h : P`, `generalize h : e = x`, …
  const LOCAL_DECL = new RegExp(`\\b(?:have|haveI|replace|let|suffices|obtain|by_cases!?|generalize|if)\\s+(${NAME_CHARS})((?:\\s*[({\\[⦃][^(){}\\[\\]⦃⦄]*[)}\\]⦄])*)\\s*:(?!=)`, 'g');

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

  /** End of an unbracketed binder's type: first top-level `=>`, `↦` or `,`. */
  function binderBodyStart(text, start) {
    let depth = 0;
    for (let i = start; i < text.length; i++) {
      const ch = text[i];
      if (OPENERS[ch]) depth++;
      else if (CLOSERS.has(ch)) { if (depth === 0) return i; depth--; }
      else if (depth === 0 && (ch === ',' || ch === '↦' || text.startsWith('=>', i) || text.startsWith(' in ', i))) return i;
    }
    return text.length;
  }

  /** End of a `have h : T` type: first top-level `:=`, ` by`, or end of line. */
  function localDeclTypeEnd(text, start) {
    // The type may continue on following lines that are indented deeper than the `have`.
    const lineStart = text.lastIndexOf('\n', start - 1) + 1;
    const indent = (text.slice(lineStart).match(/^[ \t]*/) || [''])[0].length;
    let depth = 0;
    for (let i = start; i < text.length; i++) {
      const ch = text[i];
      if (OPENERS[ch]) depth++;
      else if (CLOSERS.has(ch)) depth = Math.max(0, depth - 1);
      else if (ch === '\n') {
        const nextIndent = (text.slice(i + 1).match(/^[ \t]*/) || [''])[0].length;
        if (depth === 0 && nextIndent <= indent) return i;
      } else if (depth === 0) {
        if (text.startsWith(':=', i)) return i;
        if (/^\sby\b/.test(text.slice(i, i + 4))) return i;
        if (/^\sthen\b/.test(text.slice(i, i + 6))) return i;
      }
    }
    return text.length;
  }

  /**
   * Find the declared type of local `name` in `text` (source order).
   * The last binder wins, as it shadows earlier ones.
   */
  function findBinderType(name, text) {
    const r = findBinder(name, text);
    return r ? r.type : null;
  }

  /** Like findBinderType, plus where the binder is: { type, pos }. */
  /** End of a declaration header (its top-level ` : `, `:=`, `where` or `|`), or -1 if `text` isn't a declaration. */
  function headerEnd(text) {
    const m = text.match(DECL_START);
    if (!m) return -1;
    let depth = 0;
    for (let i = m[0].length; i < text.length; i++) {
      const ch = text[i];
      if (OPENERS[ch]) depth++;
      else if (CLOSERS.has(ch)) depth = Math.max(0, depth - 1);
      else if (depth === 0) {
        if (ch === ':' || ch === '|') return i;
        if (/^\swhere\b/.test(text.slice(i, i + 7))) return i;
      }
    }
    return text.length;
  }

  /** Is the `(` at `i` (after the header) a binder, i.e. preceded by `fun`/`∀`/… possibly through other binder groups? */
  function binderKeywordBefore(text, i) {
    let k = i - 1;
    for (;;) {
      while (k >= 0 && /\s/.test(text[k])) k--;
      if (k < 0) return false;
      if (CLOSERS.has(text[k])) {
        // Skip a previous group `(x : T)` back to its opener.
        let depth = 0;
        for (; k >= 0; k--) {
          if (CLOSERS.has(text[k])) depth++;
          else if (OPENERS[text[k]]) { depth--; if (depth === 0) break; }
        }
        k--;
        continue;
      }
      return /(?:\bfun|λ|∀|∃!?|Π|∑'?|∏'?|⋃|⋂|⨆|⨅|∫|∮|\bhave\s+[^\s:()]+|\blet\s+[^\s:()]+)$/.test(text.slice(Math.max(0, k - 20), k + 1));
    }
  }

  function findBinder(name, text) {
    if (!name || !text) return null;
    let found = null;
    let foundPos = -1;
    const hdrEnd = headerEnd(text);

    for (let i = 0; i < text.length; i++) {
      const ch = text[i];
      if (ch !== '(' && ch !== '{' && ch !== '⦃' && ch !== '[') continue;
      const m = text.slice(i + 1).match(BINDER_NAMES);
      if (!m) continue;
      const names = m[1].trim().split(/\s+/);
      if (!names.includes(name)) continue;
      // `(map f p : Set _)` in a proof is a type ascription, not a binder.
      if (ch === '(' && hdrEnd !== -1 && i > hdrEnd && !binderKeywordBefore(text, i)) continue;
      let close = matchClose(text, i);
      // A binder whose type continues past the hovered line: take what we have.
      if (close === -1) close = text.length;
      found = text.slice(i + 1 + m[0].length, close);
      // Set-builder `{z : ℂ | P z}`: the type ends at ` | `.
      if (ch === '{') {
        const bar = found.indexOf(' | ');
        if (bar !== -1) found = found.slice(0, bar);
      }
      foundPos = i;
    }

    LOCAL_DECL.lastIndex = 0;
    let lm;
    while ((lm = LOCAL_DECL.exec(text)) !== null) {
      if (lm[1] !== name) continue;
      const start = lm.index + lm[0].length;
      // Keep whichever occurrence comes later in the text.
      if (lm.index > foundPos) {
        found = text.slice(start, localDeclTypeEnd(text, start));
        const params = (lm[2] || '').trim();
        if (params) found = `∀ ${params}, ${found.trim()}`;
        foundPos = lm.index;
      }
    }

    // Unbracketed binders: `fun g : T => …`, `∀ x y : T, …`, `∃ x : T, …`.
    BINDER_KW.lastIndex = 0;
    let bm;
    while ((bm = BINDER_KW.exec(text)) !== null) {
      if (!bm[1].trim().split(/\s+/).includes(name)) continue;
      if (bm.index <= foundPos) continue;
      const start = bm.index + bm[0].length;
      found = text.slice(start, binderBodyStart(text, start));
      foundPos = bm.index;
    }

    return found ? { type: found.replace(/\s+/g, ' ').trim(), pos: foundPos } : null;
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
    if (t.startsWith('(')) {
      const close = matchClose(t, 0);
      const after = close > 0 ? t.slice(close + 1).match(/^\.([A-Z][\w'\u2080-\u2089]*)/) : null;
      if (after) return after[1];
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

  /**
   * For text ending in `(…).`, the expression inside the parentheses (which may span
   * lines); null otherwise.
   */
  function parenReceiver(prefixText) {
    const t = (prefixText || '').replace(/\s+$/, '');
    if (!t.endsWith(').')) return null;
    const close = t.length - 2;
    let depth = 0;
    for (let k = close; k >= 0; k--) {
      const ch = t[k];
      if (ch === ')') depth++;
      else if (ch === '(') {
        depth--;
        if (depth === 0) return t.slice(k + 1, close).trim();
      }
    }
    return null;
  }

  /** Leading identifier of an application `f a b`, e.g. `ContinuousAt.tendsto (h := …)` → `ContinuousAt.tendsto`. */
  function applicationHead(expr) {
    const m = (expr || '').match(/^@?([A-Za-z_\u0370-\u03FF][\w'.\u0370-\u03FF\u2080-\u2089!?]*)/);
    return m ? m[1].replace(/\.+$/, '') : null;
  }

  /**
   * Namespace that `receiver.field` resolves in, given the declaration text up to the hover.
   */
  function inferReceiverNamespace(receiver, contextText) {
    const binderType = localType(receiver, contextText);
    if (!binderType) return null;
    const resolveVar = (v) => {
      if (v === receiver) return null;
      const vt = findBinderType(v, contextText);
      return vt ? typeHead(vt, null) : null;
    };
    return typeHead(binderType, resolveVar);
  }

  /** Lines (source order) from the enclosing declaration's start through `currentIdx`. */
  function declarationContext(rawLines, currentIdx, maxLines = 400) {
    // Hunk headers carry git's enclosing-function context after the second `@@`.
    const lines = rawLines.map(l => l.replace(/^@@[^@]*@@\s?/, ''));
    const from = Math.max(0, currentIdx - maxLines);
    let start = from;
    for (let i = currentIdx; i >= from; i--) {
      if (DECL_START.test(lines[i])) { start = i; break; }
    }
    return lines.slice(start, currentIdx + 1).join('\n');
  }

  const LINE_SELECTORS = [
    '.blob-code-inner',
    '[data-tag="diff-line"]',
    '[data-component="diff-line"]',
    '.react-code-text',
    'td.blob-code'
  ];

  const FILE_SELECTORS =
    '.file, .js-file, [data-details-container-group="file"], [data-component="diff-file"], ' +
    '[data-tag="diff-entry"], section[data-file-path], div[data-file-path], table, pre';

  function isDeletion(el) {
    return el.getAttribute('data-code-marker') === '-' ||
      (el.classList && (el.classList.contains('blob-code-deletion') || el.classList.contains('diff-line-deletion'))) ||
      Boolean(el.closest && el.closest('.blob-code-deletion, .diff-line-deletion'));
  }

  /**
   * The lines of the hovered DOM node's file in the diff, with the hovered line's index:
   * { lines, idx } or null. Deleted lines are skipped unless the hover is on one.
   */
  function domLines(node) {
    const d = domLineEls(node);
    return d ? { lines: d.els.map(d.text), idx: d.idx } : null;
  }

  /** Like `domLines`, with the line elements and a reader: { els, idx, text(el) } or null. */
  function domLineEls(node) {
    const el = node && (node.nodeType === 1 ? node : node.parentElement);
    if (!el || !el.closest) return null;
    for (const sel of LINE_SELECTORS) {
      const lineEl = el.closest(sel);
      if (!lineEl) continue;
      const fileEl = lineEl.closest(FILE_SELECTORS) || document;
      const onDeletion = isDeletion(lineEl);
      const all = Array.from(fileEl.querySelectorAll(sel)).filter(l => l === lineEl || isDeletion(l) === onDeletion);
      const idx = all.indexOf(lineEl);
      if (idx === -1) continue;
      return { els: all, idx, text: (l) => l.textContent || '' };
    }
    return rowLineEls(el);
  }

  /** Declaration text around the hovered DOM node, read from the diff. */
  function contextFromDom(node) {
    const d = domLines(node);
    return d ? declarationContext(d.lines, d.idx) : '';
  }

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

  const ROW_SEL = 'tr, [role="row"]';
  const CELL_SEL = 'td, th, [role="gridcell"], [role="cell"]';
  const DELETION_HINT = /\b[\w-]*(deletion|deleted|removed)\b/i;

  function rowIsDeletion(row, cell) {
    if (!cell) return false;
    if (cell.getAttribute('data-code-marker') === '-') return true;
    for (let e = cell; e && e !== row.parentElement; e = e.parentElement) {
      if (typeof e.className === 'string' && DELETION_HINT.test(e.className)) return true;
    }
    // Newer views mark the line inside the cell: `<code class="… deletion">`.
    for (const d of cell.querySelectorAll('[class]')) {
      if (typeof d.className === 'string' && DELETION_HINT.test(d.className)) return true;
    }
    const marker = cell.querySelector('.diff-text-marker');
    return Boolean(marker && marker.textContent.trim() === '-');
  }

  /** Code text of a diff cell, without a rendered `+`/`-` marker. */
  function cellCodeText(cell) {
    const inner = cell.querySelector('.diff-text-inner, .blob-code-inner');
    return inner ? inner.textContent || '' : stripMarker(cell.textContent || '');
  }

  /** Strip a diff marker GitHub may render as text (`+theorem …`, `-  exact …`). */
  function stripMarker(text) {
    return text.replace(/^\n+/, '').replace(/^\+/, '').replace(/^-(?!-)/, '');
  }

  /**
   * Markup-agnostic fallback: read the same column of every row in the hovered line's table.
   * Works for GitHub's newer diff views, whose class names we don't hard-code.
   */
  function contextFromRows(el) {
    const d = rowLineEls(el);
    return d ? declarationContext(d.els.map(d.text), d.idx) : '';
  }

  /** Up to `span` lines of the same diff column (and side) before and after the hovered row. */
  function nearbyRowLines(el, span) {
    const row = el.closest(ROW_SEL);
    const cell = el.closest(CELL_SEL);
    if (!row || !cell) return null;
    const cellsOf = (r) => Array.from(r.children).filter(c => c.matches(CELL_SEL));
    const col = cellsOf(row).indexOf(cell);
    if (col === -1) return null;
    const onDeletion = rowIsDeletion(row, cell);
    const take = (next) => {
      const out = [];
      for (let r = next(row); r && out.length < span; r = next(r)) {
        const c = cellsOf(r)[col];
        if (c && rowIsDeletion(r, c) === onDeletion) out.push(c);
      }
      return out;
    };
    const before = take(r => r.previousElementSibling).reverse();
    const after = take(r => r.nextElementSibling);
    const cells = [...before, cell, ...after];
    return { lines: cells.map(cellCodeText), cells, idx: before.length };
  }

  function rowLineEls(el) {
    const row = el.closest(ROW_SEL);
    const cell = el.closest(CELL_SEL);
    if (!row || !cell) return null;
    const table = row.closest('table, [role="grid"], [role="table"]') || row.parentElement;
    if (!table) return null;
    const cellsOf = (r) => Array.from(r.children).filter(c => c.matches(CELL_SEL));
    const col = cellsOf(row).indexOf(cell);
    if (col === -1) return null;
    const onDeletion = rowIsDeletion(row, cell);

    const cells = [];
    let idx = -1;
    for (const r of table.querySelectorAll(ROW_SEL)) {
      if (r.closest('table, [role="grid"], [role="table"]') !== table && r !== row) continue;
      const c = cellsOf(r)[col];
      if (!c) continue;
      if (r !== row && rowIsDeletion(r, c) !== onDeletion) continue;
      if (r === row) idx = cells.length;
      cells.push(c);
    }
    return idx === -1 ? null : { els: cells, idx, text: cellCodeText };
  }

  // --- Local variables: show the type of a hovered binder ---

  const IDENT_SPLIT = /[^A-Za-z0-9_'!?\u2080-\u2089\u0370-\u03FF\u1F00-\u1FFF]+/;
  const namesIn = (s) => s.split(IDENT_SPLIT).filter(Boolean);

  /**
   * How `name` is bound when the source gives no type: `intro x`, `fun x =>`,
   * `obtain ⟨x, hx⟩ := …`, `rcases h with ⟨x, hx⟩`, `| succ n ih =>`, `∀ x,`,
   * or `let/set x := v`. Returns { how, value? } for the latest binding, or null.
   */
  function findUntypedBinder(name, text) {
    if (!name || !text) return null;
    let best = null;
    const consider = (pos, how, value) => { if (!best || pos >= best.pos) best = { pos, how, value }; };
    const scan = (re, how, group = 1) => {
      re.lastIndex = 0;
      let m;
      while ((m = re.exec(text)) !== null) {
        if (namesIn(m[group]).includes(name)) consider(m.index, how);
      }
    };
    scan(/\b(?:intro|intros|introv|rintro)\b([^\n]*)/g, 'introduced by a tactic');
    scan(/\bfun\b([^\n]*?)(?:=>|↦)/g, 'bound by `fun`');
    scan(/\bobtain\s+([^\n]*?)(?::=|\s:\s|$)/gm, 'destructured by `obtain`');
    scan(/\brcases\b[^\n]*\bwith\b([^\n]*)/g, 'destructured by `rcases`');
    scan(/\bfilter_upwards\b[^\n]*\bwith\b([^\n]*)/g, 'introduced by `filter_upwards`');
    scan(/(?:\]|^)\s*with\b([^\n|]*)$/gm, 'introduced by a tactic `with` clause');
    scan(/\b(?:induction|cases|ext|funext|choose|peel)\b[^\n]*\bwith\b([^\n|]*)$/gm, 'introduced by a tactic');
    scan(/^\s*\|\s*[\w.']+([^\n]*?)=>/gm, 'bound in a match / induction case');
    scan(/(?:∀|∃|Π|λ)\s+([^:,\n]*?),/g, 'bound by a quantifier');
    scan(/(?:∑'?|∏'?|⋃|⋂|⨆|⨅|∫|∮)\s+([^:,\n]*?)\s*(?:\bin\b|∈|,)/g, 'bound by a big operator / integral');
    scan(/\b(?:by_contra!?|by_contra'|contrapose!?|by_cases!?)\s+([^\s:]+)\s*$/gm, 'introduced by `by_contra` / `by_cases`');
    scan(/\{\s*([^:{}|]+?)\s*\|(?!\|)/g, 'bound in a set-builder');
    scan(/\bset\s+[^\n]*?\bwith\s+←?\s*([^\s]+)/g, 'introduced by `set … with`');
    scan(/\b(?:ext|funext|ext1)\s+([^:\n]*?)\s*(?:$|:)/gm, 'introduced by `ext`');
    scan(/^\s*[\w'\u2080-\u2089]+((?:\s+[\w'\u0370-\u03FF\u2080-\u2089]+)+)\s*:=/gm, 'an argument of a structure field definition');
    // Untyped binder groups in a declaration header: `theorem coe_mk (f : …) (h₁ h₂) : …`.
    const hdr = headerEnd(text);
    if (hdr > 0) {
      const header = text.slice(0, hdr);
      const groupRe = /[({⦃]\s*([^(){}⦃⦄:\[\]]+?)\s*[)}⦄]/g;
      let gm;
      while ((gm = groupRe.exec(header)) !== null) {
        if (namesIn(gm[1]).includes(name) && !/[^\s\w'\u0370-\u03FF\u2080-\u2089]/.test(gm[1])) {
          consider(gm.index, 'a binder of this declaration without a written type');
        }
      }
    }
    const defRe = /\b(?:let|set|have)\s+([^\s:=()]+)(?:\s*[({⦃[](?:[^(){}⦃⦄[\]]|[({[][^(){}[\]]*[)}\]])*[)}⦄\]])*\s*:=\s*([^\n]*?)(?:\bwith\b|$)/gm;
    let dm;
    while ((dm = defRe.exec(text)) !== null) {
      if (dm[1] === name) consider(dm.index, 'defined locally', dm[2].trim());
    }
    return best ? { how: best.how, value: best.value, pos: best.pos } : null;
  }

  // --- Type inference for locals without a written type ---

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

  /** rcases-style pattern → { name } | { alt: [...] } | { tuple: [...] } | { other }. */
  function parsePattern(p) {
    p = stripParens(p);
    const alts = splitTop(p, '|');
    if (alts.length > 1) return { alt: alts.map(parsePattern) };
    if (p.startsWith('⟨') && matchClose(p, 0) === p.length - 1) return { tuple: splitTop(p.slice(1, -1), ',').map(parsePattern) };
    if (/^[^\s()⟨⟩,|:]+$/.test(p)) return { name: p };
    return { other: p };
  }

  const LETTERS = ['first', 'second', 'third', 'fourth', 'fifth', 'sixth'];

  /** Element type of a set expression, when it shows: `{z : ℂ | …}`, `A ×ℂ B`, `Set.Icc (0 : ℝ) s`, `s : Set T`. */
  function elementTypeOf(setExpr, text, depth = 0) {
    const S = stripParens(setExpr);
    if (!S || depth > 3) return null;
    let m = S.match(/^\{\s*[^:{}|]+?\s*:\s*([^|{}]+?)\s*(?:\||\/\/)/);
    if (m) return m[1].trim();
    if (topLevelIndexOf(S, '×ℂ') > 0) return 'ℂ';
    const prod = topLevelIndexOf(S, '×ˢ');
    if (prod > 0) {
      const a = elementTypeOf(S.slice(0, prod), text, depth + 1);
      const b = elementTypeOf(S.slice(prod + 2), text, depth + 1);
      return a && b ? `${a} × ${b}` : null;
    }
    for (const op of ['∩', '∪', '\\']) {
      const i = topLevelIndexOf(S, op);
      if (i > 0) return elementTypeOf(S.slice(0, i), text, depth + 1) || elementTypeOf(S.slice(i + 1), text, depth + 1);
    }
    const [head, ...args] = splitApp(S);
    const key = (head || '').split('.').pop();
    if (/^(Icc|Ico|Ioc|Ioo|uIcc|uIoc|Ici|Iic|Ioi|Iio|uIoo)$/.test(key)) {
      for (const a of args) {
        const asc = a.match(/^\((.+) : (.+)\)$/);
        if (asc) return asc[2].trim();
        const t = /^[\w'Ͱ-Ͽ₀-ₜ]+$/.test(a) ? findBinderType(a, text) : null;
        if (t) return t;
      }
      return null;
    }
    if (args.length === 0 && /^[\w'Ͱ-Ͽ₀-ₜ]+$/.test(S)) {
      const t = findBinderType(S, text);
      m = t && t.match(/^(?:Set|Finset)\s+(.+)$/);
      if (m) return stripParens(m[1]);
    }
    return null;
  }

  /** Split the first component off a type for an anonymous-constructor pattern: [component, rest]. */
  function splitProduct(type, pat) {
    const t = stripParens(type);
    if (!t) return [null, null];
    if (t.startsWith('∃')) {
      const comma = topLevelIndexOf(t, ',');
      if (comma === -1) return [null, null];
      let binder = t.slice(1, comma).trim().replace(/^!/, '').trim();
      let body = t.slice(comma + 1).trim();
      binder = stripParens(binder);
      let v, ty = null, pred = null;
      const pm = binder.match(/^([^\s:]+)\s*(∈|∉|<|≤|>|≥|≠|⊆)\s*(.+)$/);
      if (pm) { v = pm[1]; pred = `${pm[2]} ${pm[3]}`; ty = pm[2] === '∈' ? elementTypeOf(pm[3], '') : null; }
      else {
        const c = binder.indexOf(':');
        const names = (c === -1 ? binder : binder.slice(0, c)).trim().split(/\s+/);
        v = names[0];
        ty = c === -1 ? null : binder.slice(c + 1).trim();
        if (names.length > 1) body = `∃ ${names.slice(1).join(' ')}${ty ? ' : ' + ty : ''}, ${body}`;
      }
      if (pred) body = `${v} ${pred} ∧ ${body}`;
      if (pat && pat.name && pat.name !== v) body = replaceWord(body, v, pat.name);
      return [ty, body];
    }
    const and = topLevelIndexOf(t, '∧');
    if (and > 0) return [stripParens(t.slice(0, and)), stripParens(t.slice(and + 1))];
    const iff = topLevelIndexOf(t, '↔');
    if (iff > 0) {
      const a = stripParens(t.slice(0, iff)), b = stripParens(t.slice(iff + 1));
      return [`${a} → ${b}`, `${b} → ${a}`];
    }
    return [null, null];
  }

  /** Assign types to the names in `pat` by destructuring a value of `type`. out: Map name → [{ type, tag }]. */
  function destructure(pat, type, out, tag = null) {
    const put = (n, t) => {
      if (['rfl', '_', '-'].includes(n)) return;
      if (!out.has(n)) out.set(n, []);
      out.get(n).push({ type: t || null, tag });
    };
    if (pat.name) return put(pat.name, type ? stripParens(type) : null);
    if (pat.alt) {
      const parts = [];
      let t = type ? stripParens(type) : null;
      for (let k = 0; k < pat.alt.length; k++) {
        if (!t) { parts.push(null); continue; }
        const i = k < pat.alt.length - 1 ? topLevelIndexOf(t, '∨') : -1;
        if (i > 0) { parts.push(stripParens(t.slice(0, i))); t = stripParens(t.slice(i + 1)); }
        else { parts.push(t); t = null; }
      }
      pat.alt.forEach((p, k) => destructure(p, parts[k], out, k + 1));
      return;
    }
    if (pat.tuple) {
      let t = type;
      pat.tuple.forEach((p, k) => {
        if (k === pat.tuple.length - 1) return destructure(p, t, out, tag);
        const [first, rest] = t ? splitProduct(t, p) : [null, null];
        destructure(p, first, out, tag);
        t = rest;
      });
    }
  }

  /** Peel binders/premises off goal `target` for `intro`-style patterns. */
  function peelGoal(target, patterns, text) {
    const out = new Map();
    let t = stripParens(target);
    for (const pat of patterns) {
      t = stripParens(t);
      if (!t) { destructure(pat, null, out); continue; }
      if (/^(∀|Π)/.test(t)) {
        const comma = topLevelIndexOf(t, ',');
        if (comma === -1) { destructure(pat, null, out); t = null; continue; }
        const seg = t.slice(1, comma).trim();
        let body = t.slice(comma + 1).trim();
        // Binder list → [{ v, type, pred }]
        const binders = [];
        if (OPENERS[seg[0]]) {
          let i = 0;
          while (i < seg.length) {
            while (seg[i] === ' ') i++;
            if (!OPENERS[seg[i]]) break;
            const close = matchClose(seg, i);
            if (close === -1) break;
            const g = seg.slice(i + 1, close);
            const c = g.indexOf(':');
            const names = (c === -1 ? g : g.slice(0, c)).trim().split(/\s+/);
            names.forEach(v => binders.push({ v, type: c === -1 ? null : g.slice(c + 1).trim() }));
            i = close + 1;
          }
        } else {
          const pm = seg.match(/^([\w'\u0370-\u03FF\u2080-\u209C\s]+?)\s*(∈|∉|<|≤|>|≥|≠|⊆)\s*(.+)$/);
          if (pm) {
            pm[1].trim().split(/\s+/).forEach(v => binders.push({
              v, type: pm[2] === '∈' ? elementTypeOf(pm[3], text) : null, pred: `${pm[2]} ${pm[3]}`
            }));
          } else {
            const c = seg.indexOf(':');
            const names = (c === -1 ? seg : seg.slice(0, c)).trim().split(/\s+/);
            names.forEach(v => binders.push({ v, type: c === -1 ? null : seg.slice(c + 1).trim() }));
          }
        }
        if (binders.length === 0) { destructure(pat, null, out); t = null; continue; }
        const [b, ...rest] = binders;
        if (rest.length) {
          const groups = rest.map(r => r.pred ? null : `(${r.v}${r.type ? ' : ' + r.type : ''})`);
          if (groups.every(Boolean)) body = `∀ ${groups.join(' ')}, ${body}`;
          else body = `∀ ${rest.map(r => r.v).join(' ')} ${rest[0].pred}, ${body}`;
        }
        if (b.pred) body = `${b.v} ${b.pred} → ${body}`;
        if (pat.name && pat.name !== b.v) body = replaceWord(body, b.v, pat.name);
        destructure(pat, b.type, out);
        t = body;
        continue;
      }
      // Premise `A → B` (plain arrow, not a bundled-map notation).
      let depth = 0, cut = -1;
      for (let k = 0; k < t.length; k++) {
        const ch = t[k];
        if (OPENERS[ch]) depth++;
        else if (CLOSERS.has(ch)) depth = Math.max(0, depth - 1);
        else if (depth === 0 && ch === '→' && t[k + 1] === ' ') { cut = k; break; }
      }
      if (cut > 0) {
        destructure(pat, t.slice(0, cut), out);
        t = t.slice(cut + 1);
        continue;
      }
      if (t.startsWith('¬')) { destructure(pat, t.slice(1), out); t = 'False'; continue; }
      const sub = topLevelIndexOf(t, '⊆');
      if (sub > 0) {
        const A = stripParens(t.slice(0, sub)), B = stripParens(t.slice(sub + 1));
        destructure(pat, elementTypeOf(A, text) || elementTypeOf(B, text), out);
        const v = pat.name || 'x';
        t = `${v} ∈ ${A} → ${v} ∈ ${B}`;
        continue;
      }
      destructure(pat, null, out);
      t = null;
    }
    return out;
  }

  /** Line index and start offsets for `text`. */
  function lineTable(text) {
    const starts = [0];
    for (let i = 0; i < text.length; i++) if (text[i] === '\n') starts.push(i + 1);
    return starts;
  }

  /**
   * Goal of the `by` block an `intro`/`fun` at `pos` opens: the declaration's statement or a
   * `have`'s type, provided only other intros come before it in the block.
   * Returns { target, patterns } (all intro patterns of the block up to `pos`) or null.
   */
  function introGoal(text, pos, kind) {
    const starts = lineTable(text);
    let li = starts.length - 1;
    while (starts[li] > pos) li--;
    const lineAt = (i) => text.slice(starts[i], i + 1 < starts.length ? starts[i + 1] - 1 : text.length);
    const isIntroLine = (l) => /^\s*(?:·\s*)?(intro|intros|rintro)\b/.test(l);

    // Find the line whose `by` (or `:=` for term-mode `fun`) opens this block.
    let byLine = -1;
    const own = text.slice(starts[li], pos);
    if (/(?::=\s*by|\bby)\s*(?:·\s*)?(?:(?:exact|refine|apply)\s+)?$/.test(own) || (kind === 'fun' && /:=\s*$/.test(own))) {
      byLine = li;
    } else if (/^\s*(?:·\s*)?(?:(?:exact|refine|apply)\s+)?$/.test(own)) {
      let j = li - 1;
      while (j >= 0 && (isIntroLine(lineAt(j)) || !lineAt(j).trim())) j--;
      if (j >= 0 && (/\bby\s*$/.test(lineAt(j).replace(/--.*$/, '')) || (kind === 'fun' && /:=\s*$/.test(lineAt(j))))) byLine = j;
    }
    if (byLine === -1) return null;
    const byEnd = byLine + 1 < starts.length ? starts[byLine + 1] - 1 : text.length;
    const upToBy = text.slice(0, byEnd);
    const assign = upToBy.lastIndexOf(':=');
    if (assign === -1) return null;

    // `have h (params) : T := by` ending on the by-line (latest wins), else the declaration statement.
    let target = null;
    LOCAL_DECL.lastIndex = 0;
    let lm;
    while ((lm = LOCAL_DECL.exec(upToBy)) !== null) {
      const start = lm.index + lm[0].length;
      const end = localDeclTypeEnd(upToBy, start);
      if (end === assign || upToBy.slice(end, assign).trim() === '') {
        target = upToBy.slice(start, end);
        if ((lm[2] || '').trim()) target = null; // binders before the colon: skip, rare
      }
    }
    if (!target) {
      const hdr = headerEnd(text);
      if (hdr > 0 && text[hdr] === ':') {
        const stmtEnd = text.indexOf(':=', hdr);
        if (stmtEnd === assign) target = text.slice(hdr + 1, stmtEnd);
      }
    }
    if (!target) return null;

    // Patterns of every intro in the block, in order, up to and including the one at `pos`.
    const patterns = [];
    for (let i = byLine; i <= li; i++) {
      let l = lineAt(i);
      if (i === byLine) l = l.slice(l.search(/\bby\b|:=\s*$/) + 2);
      const m = kind === 'fun'
        ? l.match(/\bfun\s+(.*?)\s*(?:=>|↦)/)
        : l.match(/\b(?:intro|intros|rintro)\s+(.*)$/);
      if (!m) continue;
      splitTop(m[1].replace(/--.*$/, '').trim(), ' ').filter(Boolean).forEach(p => patterns.push(parsePattern(p)));
    }
    return { target, patterns };
  }

  /** Which `·` case of an `rcases`/`obtain` at `pos` contains the end of `text` (1-based), or 0. */
  function caseIndexAt(text, pos) {
    const starts = lineTable(text);
    let li = starts.length - 1;
    while (starts[li] > pos) li--;
    const lines = text.split('\n');
    const indent = (lines[li].match(/^\s*(?:·\s*)?/) || [''])[0].replace('·', ' ').length;
    let k = 0;
    for (let i = li + 1; i < lines.length; i++) {
      const m = lines[i].match(/^(\s*)·/);
      if (m && m[1].length === indent) k++;
      else if (lines[i].trim() && (lines[i].match(/^\s*/) || [''])[0].length < indent) return 0;
    }
    return k;
  }

  /**
   * Inferred type(s) of an untyped local `name`: { types: [{ type, tag }], source, pending? }.
   * `pending` asks the worker to type a constant application (`obtain h | h := le_or_gt b 1`).
   */
  function inferLocalType(name, text) {
    const untyped = findUntypedBinder(name, text);
    if (!untyped) return null;
    const pos = untyped.pos;
    const lineEnd = text.indexOf('\n', pos) === -1 ? text.length : text.indexOf('\n', pos);
    const line = text.slice(pos, lineEnd);
    const result = (map, source) => {
      const types = (map.get(name) || []).filter(x => x.type);
      return types.length ? { types, source } : null;
    };

    // intro / rintro / fun: peel the goal.
    if (/^(?:intro|intros|introv|rintro)\b/.test(line) || /^fun\b/.test(line)) {
      const goal = introGoal(text, pos, /^fun\b/.test(line) ? 'fun' : 'intro');
      if (goal) return result(peelGoal(goal.target, goal.patterns, text), `the goal \`${stripParens(goal.target).slice(0, 80)}\``);
      return null;
    }

    // obtain PAT := TERM / rcases TERM with PAT
    let pat = null, term = null;
    let m = line.match(/^obtain\s+(.+?)\s*:=\s*(.+)$/);
    if (m) { pat = m[1]; term = m[2]; }
    m = !pat && line.match(/^rcases\s+(.+?)\s+with\s+(.+)$/);
    if (m) { term = m[1]; pat = m[2]; }
    if (pat && term) {
      const tree = parsePattern(pat);
      const caseIdx = /\|/.test(pat) ? caseIndexAt(text, pos) : 0;
      term = term.replace(/\s*--.*$/, '').trim();
      const head = applicationHead(term);
      const headType = head && /^[\w'Ͱ-Ͽ₀-ₜ]+$/.test(head) ? findBinderType(head, text) : null;
      if (headType) {
        // Local term: its type (after arguments, for `h x y`).
        const ty = splitApp(term).length > 1 ? conclusionOf(headType) : headType;
        const r = result((() => { const o = new Map(); destructure(tree, ty, o); return o; })(), `\`${term}\``);
        if (r) r.caseIdx = caseIdx;
        return r;
      }
      if (head) return { types: [], source: `\`${term}\``, caseIdx, pending: { pattern: pat, term, name } };
      return null;
    }

    // have x := TERM (no type): the type of TERM, from its head's signature.
    m = line.match(/^(?:have|haveI|let)\s+([^\s:=()]+)((?:\s*[({⦃[](?:[^(){}⦃⦄[\]]|[({[][^(){}[\]]*[)}\]])*[)}⦄\]])*)\s*:=\s*/);
    if (m && m[1] === name) {
      const term = fullTermAt(text, pos + m[0].length);
      if (!term || /^(by|fun|λ|⟨)\b|^[(⟨]/.test(term)) return null;
      const parts = appParts(term);
      if (!parts) return null;
      const params = m[2].trim(); // `have hag (i : ℕ) := …` has type `∀ (i : ℕ), …`
      const local = /^[\w'\u0370-\u03FF\u2080-\u209C]+$/.test(parts.head) ? localType(parts.head, text) : null;
      if (local) {
        const app = applicationTypeFrom(local, parts.positional, parts.named, text);
        return app ? { types: [{ type: params ? `∀ ${params}, ${app.type}` : app.type, tag: null }], source: `\`${parts.head}\`'s type` } : null;
      }
      return { types: [], source: `\`${term}\``, caseIdx: 0, pending: { pattern: name, term, name, params } };
    }

    // set x := v with hx
    m = line.match(/^set\s+([^\s:]+)\s*(?::\s*([^:=]+?))?\s*:=\s*(.+?)\s+with\s+←?\s*([^\s]+)/);
    if (m) {
      if (m[4] === name) return { types: [{ type: `${m[1]} = ${m[3].trim()}`, tag: null }], source: '`set … with`' };
      if (m[1] === name && m[2]) return { types: [{ type: m[2].trim(), tag: null }], source: '`set`' };
    }

    // filter_upwards [h₁, h₂] with x hx₁ hx₂: hxᵢ from hᵢ : ∀ᶠ y in l, P y
    m = text.slice(Math.max(0, text.lastIndexOf('filter_upwards', pos + 20)), lineEnd).match(/filter_upwards\s*\[([\s\S]*?)\]\s*with\s+(.+)$/);
    if (m) {
      const names = m[2].trim().split(/\s+/);
      const k = names.indexOf(name);
      const facts = splitTop(m[1], ',');
      if (k >= 1 && facts[k - 1]) {
        const ft = /^[\w'Ͱ-Ͽ₀-ₜ]+$/.test(facts[k - 1].trim()) ? findBinderType(facts[k - 1].trim(), text) : null;
        const ev = ft && ft.match(/^∀ᶠ\s+([^\s]+)(?:\s*:\s*[^,]+?)?\s+in\s+[^,]+,\s*([\s\S]+)$/);
        if (ev) return { types: [{ type: replaceWord(ev[2].trim(), ev[1], names[0]), tag: null }], source: `\`${facts[k - 1].trim()}\`` };
      }
    }
    return null;
  }

  /** Format inferred types for a tooltip: { typeSignature, note }. */
  function formatInferred(name, inferred) {
    const { types, caseIdx } = inferred;
    const tagged = types.filter(t => t.tag);
    if (tagged.length && caseIdx && types.find(t => t.tag === caseIdx)) {
      const t = types.find(x => x.tag === caseIdx);
      return { typeSignature: `${name} : ${t.type}`, note: `in the ${LETTERS[caseIdx - 1] || caseIdx + 'th'} case` };
    }
    if (tagged.length > 1) {
      return {
        typeSignature: `${name} : ${tagged[0].type}`,
        note: 'by case: ' + tagged.map(t => `${LETTERS[t.tag - 1] || t.tag}: \`${t.type}\``).join('; ')
      };
    }
    return { typeSignature: `${name} : ${types[0].type}`, note: null };
  }

  /** Tooltip data for a local variable hovered in `contextText`, or null if it isn't one. */
  function localVariableInfo(name, contextText) {
    // `rfl` in `rintro rfl` / `obtain rfl | h` is a pattern (it substitutes), not a variable.
    if (!name || name.includes('.') || !contextText || name === 'rfl') return null;
    let binder = findBinder(name, contextText);
    const later = binder && findUntypedBinder(name, contextText);
    let shadowed = null;
    if (later && later.pos > binder.pos) {
      // `intro x` after an earlier `∀ x : T`: prefer what the intro gives, else fall back to T.
      let inferred = null;
      try { inferred = inferLocalType(name, contextText); } catch (err) { inferred = null; }
      if (inferred && inferred.types.length) binder = null;
      else shadowed = binder;
    }
    if (shadowed) {
      return withReplay({
        name, kind: 'variable', source: 'local_var',
        typeSignature: `${name} : ${shadowed.type}`,
        docstring: `Local variable ${later.how}; shown with the type of the earlier binder \`${name} : ${shadowed.type}\`, which it most likely re-introduces.`
      }, shadowed.type, hypothesisChanges(name, contextText, later.pos));
    }
    if (binder) {
      return withReplay({
        name, kind: 'variable', source: 'local_var',
        typeSignature: `${name} : ${binder.type}`,
        docstring: 'Local variable / hypothesis bound in this declaration.'
      }, binder.type, hypothesisChanges(name, contextText, binder.pos));
    }
    const untyped = findUntypedBinder(name, contextText);
    if (untyped) {
      let inferred = null;
      try { inferred = inferLocalType(name, contextText); } catch (err) { inferred = null; }
      const changes = hypothesisChanges(name, contextText, untyped.pos);
      if (inferred && inferred.types.length) {
        const f = formatInferred(name, inferred);
        return withReplay({
          name, kind: 'variable', source: 'local_var',
          typeSignature: f.typeSignature,
          docstring: `Local variable ${untyped.how}; type inferred from ${inferred.source}${f.note ? ' (' + f.note + ')' : ''}.`
        }, f.typeSignature.slice(name.length + 3), changes);
      }
      const info = {
        name, kind: 'variable', source: 'local_var',
        typeSignature: untyped.value ? `${name} := ${untyped.value}` : `${name} : _`,
        docstring: `Local variable ${untyped.how}; its type isn't written in the source` +
          (inferred && inferred.pending ? ', so it is being worked out from the signature…' : ', so it would need Lean to elaborate.'),
        inferNeeded: inferred && inferred.pending ? Object.assign({ caseIdx: inferred.caseIdx || 0 }, inferred.pending) : null
      };
      // A pending inference gets its base type from the worker; replay changes after that.
      return info.inferNeeded ? withReplay(info, null, changes) : info;
    }
    return null;
  }

  /**
   * Attach a replay request when tactics before the hover change the hypothesis
   * (`rw … at h`, `simp at h`, …): the type shown first is the declared one, and
   * `replayChanges` / `describeReplay` produce the current one (or say why they can't).
   */
  function withReplay(info, baseType, changes) {
    if (!changes || !changes.length) return info;
    const pendingText = changes.map(c => `\`${c.text.length > 60 ? c.text.slice(0, 57) + '…' : c.text}\``).join(', ');
    return Object.assign(info, {
      docstring: `${info.docstring}\n\n*Applying ${pendingText}…*`,
      replay: { baseType, changes, lead: info.docstring, projection: null }
    });
  }

  /** Type of a local, written or inferred (a single unambiguous type), or null. */
  function localType(name, text) {
    const b = findBinder(name, text);
    const later = b && findUntypedBinder(name, text);
    if (b && !(later && later.pos > b.pos)) return b.type;
    if (b) {
      let inferred = null;
      try { inferred = inferLocalType(name, text); } catch (err) { inferred = null; }
      if (!inferred || !inferred.types.length) return b.type;
    }
    let inferred = null;
    try { inferred = inferLocalType(name, text); } catch (err) { return null; }
    if (!inferred || !inferred.types.length) return null;
    if (inferred.types.length === 1) return inferred.types[0].type;
    const pick = inferred.caseIdx && inferred.types.find(x => x.tag === inferred.caseIdx);
    return pick ? pick.type : null;
  }

  // --- Anonymous projections: `h.1`, `h.2`, `p.2.1` ---

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

  // `x ∈ S a b` that unfold to a conjunction; `$x`, `$a`, `$b` are substituted.
  const MEMBERSHIP_CONJ = {
    'Icc': ['$a ≤ $x', '$x ≤ $b'], 'Ico': ['$a ≤ $x', '$x < $b'],
    'Ioc': ['$a < $x', '$x ≤ $b'], 'Ioo': ['$a < $x', '$x < $b'],
    'uIcc': ['$a ⊓ $b ≤ $x', '$x ≤ $a ⊔ $b'], 'uIoc': ['$a ⊓ $b < $x', '$x ≤ $a ⊔ $b']
  };

  /**
   * Type of the n-th anonymous projection (`.1`, `.2`) of a value of type `type`, when the
   * shape tells us: `∧`, `↔`, `∃`, `×`, subtypes, `x ∈ s ∩ t` and interval membership.
   * Returns { type, note? } or null (e.g. a structure: the worker can read its `mk`).
   */
  function projectionType(type, n) {
    if (!type || (n !== 1 && n !== 2)) return null;
    let t = type.replace(/\s+/g, ' ').trim();
    while (t.startsWith('(') && matchClose(t, 0) === t.length - 1) t = t.slice(1, -1).trim();
    const strip = (x) => {
      x = x.trim();
      while (x.startsWith('(') && matchClose(x, 0) === x.length - 1) x = x.slice(1, -1).trim();
      return x;
    };
    const pick = (a, b) => ({ type: strip(n === 1 ? a : b) });

    const iff = topLevelIndexOf(t, '↔');
    if (iff > 0) {
      const a = strip(t.slice(0, iff));
      const b = strip(t.slice(iff + 1));
      return { type: n === 1 ? `${a} → ${b}` : `${b} → ${a}`, note: n === 1 ? '`Iff.mp`' : '`Iff.mpr`' };
    }
    if (t.startsWith('∃')) {
      const comma = topLevelIndexOf(t, ',');
      if (comma === -1) return null;
      const binder = t.slice(1, comma).trim().replace(/^\(|\)$/g, '');
      const colon = binder.indexOf(':');
      if (n === 1) return { type: colon === -1 ? '_' : binder.slice(colon + 1).trim(), note: 'the witness' };
      return { type: strip(t.slice(comma + 1)), note: `with \`${binder.split(/[\s:]/)[0]}\` the witness` };
    }
    if (/^\{[^{}]*\/\/.*\}$/.test(t)) {
      const inner = t.slice(1, -1);
      const sep = inner.indexOf('//');
      const binder = inner.slice(0, sep).trim();
      const colon = binder.indexOf(':');
      return n === 1 ? { type: colon === -1 ? '_' : binder.slice(colon + 1).trim() } : { type: inner.slice(sep + 2).trim() };
    }
    const and = topLevelIndexOf(t, '∧');
    if (and > 0) return pick(t.slice(0, and), t.slice(and + 1)); // ∧ is right-associative
    const prod = topLevelIndexOf(t, '×');
    if (prod > 0) return pick(t.slice(0, prod), t.slice(prod + 1));

    const mem = topLevelIndexOf(t, '∈');
    if (mem > 0) {
      const x = strip(t.slice(0, mem));
      const set = strip(t.slice(mem + 1));
      const inter = topLevelIndexOf(set, '∩');
      if (inter > 0) return { type: `${x} ∈ ${strip(n === 1 ? set.slice(0, inter) : set.slice(inter + 1))}` };
      const [head, a, b] = splitApp(set);
      const key = head && head.split('.').pop();
      if (MEMBERSHIP_CONJ[key] && a !== undefined && b !== undefined && /^(Set\.)?[A-Za-z]+$/.test(head)) {
        const tpl = MEMBERSHIP_CONJ[key][n - 1];
        return { type: tpl.replace(/\$x/g, x).replace(/\$a/g, a).replace(/\$b/g, b), note: `\`${x} ∈ ${set}\` unfolds to a conjunction` };
      }
    }
    return null;
  }

  /**
   * Tactic lines after position `after` that change hypothesis `name`:
   * `rw [...] at h`, `simp at h ⊢`, `norm_num at *`, `replace h := …`, `subst`, …
   */
  function laterChanges(name, text, after) {
    const changes = [];
    const re = /^[ \t]*(?:·\s*)?(.*\b(?:rw|rwa|erw|rewrite|nth_rw|nth_rewrite|simp|simp_rw|simpa|dsimp|norm_num|push_neg|push_cast|norm_cast|field_simp|ring_nf|unfold|change|conv|lift)\b[^\n]*\bat\b([^\n]*))$/gm;
    let m;
    while ((m = re.exec(text)) !== null) {
      if (m.index <= after) continue;
      const targets = namesIn(m[2].replace(/⊢/g, ' '));
      if (targets.includes(name) || /\bat\s+\*/.test(m[1])) changes.push(m[1].trim());
    }
    const rep = new RegExp(`\\breplace\\s+${name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\b[^\n]*`, 'g');
    while ((m = rep.exec(text)) !== null) if (m.index > after) changes.push(m[0].trim());
    return changes;
  }

  function changeWarning(name, changes) {
    if (!changes.length) return '';
    const shown = changes.slice(-2).map(c => `\`${c.length > 70 ? c.slice(0, 67) + '…' : c}\``).join(', ');
    return `\n\n**Note:** \`${name}\` is changed before this point (${shown}), so its current type may differ from the one written above.`;
  }

  /**
   * Tooltip data for `h.1`, `h.2.1`, … where `h` is a local. Unknown shapes still get a
   * tooltip naming the base; `structureNeeded` asks the worker to read a structure's `mk`.
   */
  function projectionInfo(chain, contextText) {
    const segs = chain.split('.');
    if (segs.length < 2 || !/^\d+$/.test(segs[segs.length - 1]) || !segs.slice(1).every(x => /^\d+$/.test(x))) return null;
    let base = findBinder(segs[0], contextText);
    const untypedBase = findUntypedBinder(segs[0], contextText);
    if (base && untypedBase && untypedBase.pos > base.pos) base = null; // re-bound later (intro / obtain)
    if (!base) {
      if (!untypedBase) return null;
      const inferredType = localType(segs[0], contextText);
      if (!inferredType) {
        return {
          name: chain, kind: 'variable', source: 'local_var',
          typeSignature: `${chain} : _`,
          docstring: `Projection \`.${segs.slice(1).join('.')}\` of the local \`${segs[0]}\`, which is ${untypedBase.how}; its type isn't written in the source.`
        };
      }
      base = { type: inferredType, pos: untypedBase.pos };
    }
    const changes = hypothesisChanges(segs[0], contextText, base.pos);
    if (changes.length) {
      const info = {
        name: chain, kind: 'variable', source: 'local_var',
        typeSignature: `${chain} : _`,
        docstring: `Projection of \`${segs[0]}\`.`
      };
      withReplay(info, base.type, changes);
      info.replay.projection = segs.slice(1).map(Number);
      return info;
    }
    const warning = '';
    let type = base.type;
    const notes = [];
    for (let k = 1; k < segs.length; k++) {
      const proj = projectionType(type, parseInt(segs[k], 10));
      if (!proj) {
        return {
          name: chain, kind: 'variable', source: 'local_var',
          typeSignature: `${chain} : _`,
          docstring: `Projection \`.${segs.slice(k).join('.')}\` of \`${segs.slice(0, k).join('.')} : ${type}\`.` + warning,
          structureNeeded: { type, index: parseInt(segs[k], 10), rest: segs.slice(k + 1).map(Number) }
        };
      }
      if (proj.note) notes.push(proj.note);
      type = proj.type;
    }
    return {
      name: chain, kind: 'variable', source: 'local_var',
      typeSignature: `${chain} : ${type}`,
      docstring: `Projection of \`${segs[0]} : ${base.type}\`${notes.length ? ' (' + notes.join('; ') + ')' : ''}.` + warning
    };
  }

  // --- Named arguments: `foo (b := a)` ---

  const TACTIC_LEAD = /^(?:exact|refine'?|apply|use|exists|have\s+\S+\s*:=|show\s+.*\bfrom|calc|simpa\s+.*\busing|simpa\s+using|convert|specialize|obtain\s+.*:=|rcases|filter_upwards\s*\[|positivity|gcongr|linarith\s*\[|nlinarith\s*\[)\s*/;

  /**
   * For text ending in `… f a (`, where the hovered word is followed by `:=`, the
   * function being applied (`f`), possibly across lines; null if there is none.
   */
  function namedArgFunction(prefixText) {
    const t = (prefixText || '').replace(/\(\s*$/, '');
    if (t === prefixText) return null;
    let depth = 0;
    let k = t.length - 1;
    for (; k >= 0; k--) {
      const ch = t[k];
      if (CLOSERS.has(ch)) depth++;
      else if (OPENERS[ch]) { if (depth === 0) break; depth--; }
      else if (depth === 0 && (ch === ',' || ch === '←' || ch === '|' || (ch === '=' && t[k - 1] === ':'))) break;
    }
    let segment = t.slice(k + 1).replace(/\s+/g, ' ').trim();
    segment = segment.replace(TACTIC_LEAD, '');
    return applicationHead(segment);
  }

  /** Signature `fn`'s binder for named argument `arg`, as tooltip data (or null). */
  function namedArgInfo(arg, fn, signature) {
    const type = findBinderType(arg, signature || '');
    if (!type) return null;
    return {
      name: arg, kind: 'variable', source: 'local_var',
      typeSignature: `(${arg} : ${type})`,
      docstring: `Named argument \`${arg}\` of \`${fn}\`.`
    };
  }

  /**
   * The type a declaration builds (`def map … : SubMulAction R M where`), for
   * `field := …` lines in its `where` / `{ }` block. Returns the type's head or null.
   */
  function structureBeingBuilt(contextText) {
    const end = headerEnd(contextText);
    if (end === -1 || contextText[end] !== ':') return null;
    const rest = contextText.slice(end + 1);
    const stop = rest.search(/\swhere\b|:=/);
    return typeHead(stop === -1 ? rest : rest.slice(0, stop), null);
  }

  // --- Replaying `rw … at h`: a small term model ---
  //
  // Enough of Lean's notation to rewrite hypothesis types the way `rw` does: parse the type,
  // find the first instance of the rule's left side (pre-order, like `kabstract`), fix its
  // variables from that instance, replace every equal instance, and print the result.

  const T_START = /[A-Za-z_Ͱ-ΟΡ΢Τ-κμ-Ͽἀ-῿℀-⅏\u{1D400}-\u{1D7FF}]/u;
  const T_CONT = /[A-Za-z0-9_'!?Ͱ-ΟΡ΢Τ-κμ-Ͽἀ-῿₀-ₜᵢ-ᵪ℀-⅏\u{1D400}-\u{1D7FF}]/u;
  const T_OPS = ["⁻¹'", "''", "∑'", "∏'", '[[', ']]', '×ˢ', '×ℂ', '⁻¹', ':=', '<|', '|>', '=>', '∃!', '<-', '↔', '→', '←', '∧', '∨', '¬', '≠', '≤', '≥',
    '∈', '∉', '⊆', '⊂', '⊇', '⊃', '∩', '∪', '⊓', '⊔', '•', '∘', '∣', '×', 'ᶜ', '↑', '⇑', '↦', '‖', '⟨', '⟩',
    '(', ')', '[', ']', '{', '}', ',', '|', '+', '-', '*', '/', '%', '^', '=', '<', '>', '\\', '∑', '∏', '∫',
    '∀', '∃', '⋃', '⋂', '⨆', '⨅', 'λ', 'Π', '·', ':', '∞', '⊤', '⊥', '∅'];
  // [precedence, associativity] as in Lean / Mathlib.
  const T_BIN = {
    '<|': [10, 'r'], '|>': [10, 'l'], '↔': [20, 'n'], '→': [25, 'r'], '≃': [25, 'r'], '↪': [25, 'r'], '∨': [30, 'r'], '∧': [35, 'r'], '×': [35, 'r'],
    '=': [50, 'n'], '≠': [50, 'n'], '<': [50, 'n'], '>': [50, 'n'], '≤': [50, 'n'], '≥': [50, 'n'],
    '∈': [50, 'n'], '∉': [50, 'n'], '⊆': [50, 'n'], '⊂': [50, 'n'], '⊇': [50, 'n'], '⊃': [50, 'n'], '∣': [50, 'n'],
    '∪': [65, 'l'], '+': [65, 'l'], '-': [65, 'l'], '⊔': [68, 'l'], '⊓': [69, 'l'],
    '∩': [70, 'l'], '*': [70, 'l'], '/': [70, 'l'], '%': [70, 'l'], '\\': [70, 'l'], '×ℂ': [72, 'l'],
    '•': [73, 'r'], '^': [75, 'r'], '▸': [75, 'r'], "''": [80, 'l'], "⁻¹'": [80, 'l'], '×ˢ': [82, 'r'], '∘': [90, 'r']
  };
  const T_BINDER_HEADS = new Set(['∀', '∃', '∃!', '∑', '∏', "∑'", "∏'", '⋃', '⋂', '⨆', '⨅', '∫', 'λ', 'Π']);
  // Precedence of a binder notation's body (Mathlib: `∑ x ∈ s, f x` takes `term:67`, `∫ … , r:60`).
  const T_BODY_PREC = { '∑': 67, '∏': 67, "∑'": 67, "∏'": 67, '∫': 60, '⋃': 60, '⋂': 60, '⨆': 60, '⨅': 60 };
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

  const tPeek = (st) => st.toks[st.i];
  const tNext = (st) => st.toks[st.i++];
  const tIs = (t, v) => Boolean(t) && t.k === 'op' && t.v === v;
  function tExpect(st, v) { if (!tIs(tNext(st), v)) throw new Error(`expected ${v}`); }

  /** Parse a Lean term into a small AST, or null if it uses notation we don't model. */
  function parseTerm(text) {
    const st = { src: text, toks: tokenizeTerm(text), i: 0 };
    try {
      const node = tExpr(st, 0);
      return st.i === st.toks.length ? node : null;
    } catch (err) {
      return null;
    }
  }

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

  function tBinder(st, head) {
    const stops = head === 'fun' || head === 'λ' ? ['=>', '↦'] : [','];
    const binders = tRawUntil(st, stops);
    const sep = tNext(st);
    if (!sep || sep.k !== 'op' || !stops.includes(sep.v)) throw new Error('binder');
    return { k: 'bind', head, binders, sep: sep.v, body: tExpr(st, T_BODY_PREC[head] || 0) };
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
    if (!t) throw new Error('eof');
    if (t.k === 'num') return { k: 'num', v: t.v };
    if (t.k === 'id') {
      if (t.v === 'fun') return tBinder(st, 'fun');
      if (t.v === 'by') {
        // A tactic block inside a term (`⟨by simp, h⟩`, `(by positivity)`): opaque text.
        const body = tRawUntil(st, [',']);
        return { k: 'raw', v: body ? `by ${body}` : 'by', loose: true };
      }
      if (T_STOP_WORDS.has(t.v) || T_UNMODELLED.has(t.v)) throw new Error('stop word');
      return { k: 'id', v: t.v };
    }
    if (t.k === 'field') throw new Error('field');
    switch (t.v) {
      case '¬': return { k: 'pre', op: '¬', e: tExpr(st, 40) };
      case '-': return { k: 'pre', op: '-', e: tExpr(st, 75) };
      case '↑': case '⇑': return { k: 'pre', op: t.v, e: tArg(st) };
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
        if (T_BINDER_HEADS.has(t.v)) return tBinder(st, t.v);
        throw new Error(`unexpected ${t.v}`);
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
        left = { k: 'bin', op: t.v, l: left, r: right, span: [tSpan(left)[0], tSpan(right)[1]] };
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

  function tPrec(n) {
    switch (n.k) {
      case 'bin': return T_BIN[n.op][0];
      case 'pre': return n.op === '¬' ? 40 : n.op === '-' ? 75 : 2000;
      case 'post': return 1100;
      case 'app': return 1024;
      case 'bind': return T_BODY_PREC[n.head] || 0; // `∑ i ∈ s, f i ≤ c`: the body stops at `≤`
      case 'raw': return n.loose ? 0 : 2000; // text we couldn't parse: parenthesise when nested
      default: return 2000;
    }
  }

  /** Print an AST back to Lean text, adding parentheses only where precedence needs them. */
  function showTerm(n, minPrec = 0) {
    let s;
    switch (n.k) {
      case 'id': case 'num': case 'raw': s = n.v; break;
      case 'asc': s = `(${showTerm(n.e)} : ${showTerm(n.ty)})`; break;
      case 'abs': s = `|${showTerm(n.e)}|`; break;
      case 'norm': s = `‖${showTerm(n.e)}‖`; break;
      case 'tuple': s = `⟨${n.es.map(e => showTerm(e)).join(', ')}⟩`; break;
      case 'named': s = `(${n.name} := ${showTerm(n.value)})`; break;
      case 'proj': s = `${showTerm(n.e, 1025)}.${n.f}`; break;
      case 'post': s = `${showTerm(n.e, 1025)}${n.op}`; break;
      case 'pre':
        s = n.op === '¬' ? `¬${showTerm(n.e, 40)}` : n.op === '-' ? `-${showTerm(n.e, 75)}` : `${n.op}${showTerm(n.e, 1025)}`;
        break;
      case 'app': s = [showTerm(n.f, 1024), ...n.args.map(a => showTerm(a, 1025))].join(' '); break;
      case 'bin': {
        const [p, assoc] = T_BIN[n.op];
        s = `${showTerm(n.l, assoc === 'l' ? p : p + 1)} ${n.op} ${showTerm(n.r, assoc === 'r' ? p : p + 1)}`;
        break;
      }
      case 'bind':
        s = n.head === 'fun' || n.head === 'λ'
          ? `fun ${n.binders} ${n.sep} ${showTerm(n.body)}`
          : `${n.head} ${n.binders}, ${showTerm(n.body, T_BODY_PREC[n.head] || 0)}`;
        break;
      default: s = '?';
    }
    return tPrec(n) < minPrec ? `(${s})` : s;
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
      case 'bin': return [n.l, n.r];
      case 'pre': case 'post': case 'abs': case 'norm': case 'proj': case 'asc': return [n.e];
      case 'tuple': return n.es;
      case 'bind': return [n.body];
      case 'named': return [n.value];
      default: return [];
    }
  }
  function tWithChildren(n, kids) {
    switch (n.k) {
      case 'app': return Object.assign({}, n, { f: kids[0], args: kids.slice(1) });
      case 'bin': return Object.assign({}, n, { l: kids[0], r: kids[1] });
      case 'pre': case 'post': case 'abs': case 'norm': case 'proj': case 'asc': return Object.assign({}, n, { e: kids[0] });
      case 'tuple': return Object.assign({}, n, { es: kids });
      case 'bind': return Object.assign({}, n, { body: kids[0] });
      case 'named': return Object.assign({}, n, { value: kids[0] });
      default: return n;
    }
  }

  /**
   * Match pattern `p` (variables in `vars`) against term `t`, extending `sub` (Map name → node).
   * `x.field` with `x` a variable matches `t.field` (dot notation in lemma statements).
   */
  function matchTerm(p, t, vars, sub) {
    const tp = tCore(p), tt = tCore(t);
    if (!tp || !tt) return false;
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
        return Boolean(recv) && matchTerm({ k: 'id', v: tp.v.slice(0, dot) }, recv, vars, sub);
      }
    }
    // `n.succ` written as one identifier vs. a projection node of `n`.
    if (tp.k === 'proj' && tt.k === 'id' && tt.v.endsWith('.' + tp.f) && tt.v.length > tp.f.length + 1) {
      return matchTerm(tp.e, { k: 'id', v: tt.v.slice(0, tt.v.length - tp.f.length - 1) }, vars, sub);
    }
    if (tp.k === 'id' && tt.k === 'proj' && tp.v.endsWith('.' + tt.f) && tp.v.length > tt.f.length + 1) {
      return matchTerm({ k: 'id', v: tp.v.slice(0, tp.v.length - tt.f.length - 1) }, tt.e, vars, sub);
    }
    if (tp.k !== tt.k) return false;
    switch (tp.k) {
      case 'id': return tIdEq(tp.v, tt.v);
      case 'num': return tp.v === tt.v;
      case 'raw': return tRawEq(tp.v, tt.v);
      case 'abs': case 'norm': return matchTerm(tp.e, tt.e, vars, sub);
      case 'pre': case 'post': return tp.op === tt.op && matchTerm(tp.e, tt.e, vars, sub);
      case 'proj': return tp.f === tt.f && matchTerm(tp.e, tt.e, vars, sub);
      case 'tuple': return tp.es.length === tt.es.length && tp.es.every((e, i) => matchTerm(e, tt.es[i], vars, sub));
      case 'app':
        return tp.args.length === tt.args.length && matchTerm(tp.f, tt.f, vars, sub) &&
          tp.args.every((e, i) => matchTerm(e, tt.args[i], vars, sub));
      case 'bin': return tp.op === tt.op && matchTerm(tp.l, tt.l, vars, sub) && matchTerm(tp.r, tt.r, vars, sub);
      case 'named': return tp.name === tt.name && matchTerm(tp.value, tt.value, vars, sub);
      case 'bind': {
        if (tp.head !== tt.head) return false;
        const bp = binderParts(tp.binders), bt = binderParts(tt.binders);
        if (bp.names.length !== bt.names.length || bp.op !== bt.op || (bp.range === null) !== (bt.range === null)) return false;
        if (bp.range !== null) {
          const rp = bp.range.split('..'), rt = bt.range.split('..');
          if (rp.length !== rt.length) return false;
          for (let i = 0; i < rp.length; i++) {
            const a = parseTerm(rp[i]), b = parseTerm(rt[i]);
            if (a && b ? !matchTerm(a, b, vars, sub) : !tRawEq(rp[i], rt[i])) return false;
          }
        }
        // Alpha-equivalence: rename the pattern's bound variables to the target's.
        const ren = new Map(bp.names.map((nm, i) => [nm, { k: 'id', v: bt.names[i] }]));
        return matchTerm(substTerm(tp.body, ren), tt.body, vars, sub);
      }
      default: return false;
    }
  }
  const sameTerm = (a, b) => matchTerm(a, b, new Set(), new Map());

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
      return n.k === 'bind' ? Object.assign(m, { body: substTerm(n.body, sub) }) : m;
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
  function peelSignature(type) {
    let t = (type || '').replace(/\s+/g, ' ').trim();
    if (/^:(?!=)/.test(t)) t = t.slice(1).trim(); // no parameters: `: T`
    const binders = [];
    let i = 0;
    while (i < t.length && '({[⦃'.includes(t[i])) {
      const close = matchClose(t, i);
      if (close === -1) break;
      const g = t.slice(i + 1, close);
      const c = g.indexOf(' : ');
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
    const own = [...new Set(peeled.binders.flatMap(b => b.names))];
    const fresh = (n) => `__pv_${n}`;
    const ren = (str) => own.reduce((acc, n) => replaceWord(acc, n, fresh(n)), str || '');
    const binders = peeled.binders.map(b => ({ names: b.names.map(fresh), type: ren(b.type), explicit: b.explicit, bi: b.bi }));
    const vars = new Set(binders.flatMap(b => b.names));
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
    return {
      concl: ren(peeled.concl), vars, sub, own, fresh, binders, slots: allSlots, remaining: slots.slice(positional.length),
      // Arguments beyond the parameters (`hs hx` with `hs : s ⊆ t`), with their types.
      extra: positional.slice(slots.length).map((a, i) => ({ arg: a, type: opts.argTypes ? opts.argTypes[slots.length + i] : null }))
    };
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
    // A type with its variables substituted; notation we can't parse is kept as text.
    const subst = (s) => {
      if (!s || s === '_') return null;
      const n = parseTerm(s);
      return substTerm(n || { k: 'raw', v: s, loose: true }, inst.sub);
    };
    let concl = subst(inst.concl);
    if (!concl) return null;
    if (inst.extra.length) {
      // More arguments than parameters: only a few types are functions in disguise.
      if (inst.extra.length !== 1) return null;
      const c = tCore(concl);
      const argT = typeof inst.extra[0].type === 'string' ? tCore(parseTerm(inst.extra[0].type)) : null;
      if (c && c.k === 'bin' && (c.op === '⊆' || c.op === '⊂')) {
        // `hs : s ⊆ t` applied to `hx : x ∈ s` is `x ∈ t`.
        if (!argT || argT.k !== 'bin' || argT.op !== '∈' || !sameTerm(argT.r, c.l)) return null;
        concl = { k: 'bin', op: '∈', l: argT.l, r: c.r };
      } else {
        // A bundled map (`e : A ≃ B`, `f : M →+* N`) applied to a point lands in its codomain.
        const cod = codomainOf(showTerm(concl));
        const codT = cod && parseTerm(cod);
        if (!codT) return null;
        concl = codT;
      }
    }
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
      if (x.bi === '{') body = { k: 'bind', head: '∀', binders: ty ? `{${x.name} : ${ty}}` : `{${x.name}}`, sep: ',', body };
      else if (pred && !x.type) body = { k: 'bind', head: '∀', binders: `${x.name} ${body.l.op} ${showTerm(body.l.r, 51)}`, sep: ',', body: body.r };
      else if (dependent || !x.type) body = { k: 'bind', head: '∀', binders: ty ? `(${x.name} : ${ty})` : (x.name || '_'), sep: ',', body };
      else body = { k: 'bin', op: '→', l: x.type, r: body };
    }
    return body;
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
  function leanSignature(name, sig) {
    let t = (sig || '').replace(/\s+/g, ' ').trim();
    if (!t) return name;
    t = t.replace(/\[inst(?:_\d+|✝\d*)? : /g, '[');
    const univs = [];
    const add = (u) => { if (/^[a-zA-Z_][\w'\u2080-\u2089]*$/.test(u) && !['max', 'imax'].includes(u) && !univs.includes(u)) univs.push(u); };
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

  /** Head, positional and named arguments of an application `f a (b := c) d`. */
  function appParts(term) {
    const t = (term || '').trim().replace(/^@/, '');
    const head = applicationHead(t);
    if (!head) return null;
    const positional = [];
    const named = {};
    for (const a of splitApp(t).slice(1)) {
      const nm = a.match(/^\(\s*([^\s:()]+)\s*:=\s*([\s\S]+)\)$/);
      if (nm) named[nm[1]] = nm[2].trim();
      else positional.push(a);
    }
    return { head, positional, named };
  }

  /**
   * Types for a pattern bound to a term with a constant head — `obtain h | h := le_or_gt b 1`,
   * `have hb := foo hx (c := M)` — given `sigOf(name)` for constants (PR declarations, Loogle).
   * Resolves to { typeSignature, note, from, conclusion, unresolved } or null.
   */
  async function inferPending(pending, text, sigOf) {
    const parts = appParts(pending.term);
    if (!parts) return null;
    let sig = /^[\w'\u0370-\u03FF\u2080-\u209C]+$/.test(parts.head) ? localType(parts.head, text) : null;
    if (!sig && sigOf) sig = await sigOf(parts.head);
    if (!sig) return null;
    const app = applicationTypeFrom(sig, parts.positional, parts.named, text);
    if (!app) return null;
    const out = new Map();
    destructure(parsePattern(pending.pattern), app.type, out);
    const types = (out.get(pending.name) || []).filter(t => t.type)
      .map(t => (pending.params ? Object.assign({}, t, { type: `∀ ${pending.params}, ${t.type}` }) : t));
    if (!types.length) return null;
    const f = formatInferred(pending.name, { types, caseIdx: pending.caseIdx || 0 });
    return { typeSignature: f.typeSignature, note: f.note, from: parts.head, conclusion: app.type, unresolved: app.unresolved };
  }

  /** The term starting at `start`, including continuation lines indented deeper than its line. */
  function fullTermAt(text, start) {
    const ls = text.lastIndexOf('\n', start - 1) + 1;
    const indent = (text.slice(ls).match(/^\s*/) || [''])[0].length;
    let end = text.indexOf('\n', start);
    while (end !== -1) {
      const next = text.indexOf('\n', end + 1);
      const line = text.slice(end + 1, next === -1 ? text.length : next);
      if (!line.trim() || (line.match(/^\s*/) || [''])[0].length <= indent) break;
      end = next;
    }
    return text.slice(start, end === -1 ? text.length : end).replace(/--[^\n]*/g, '').replace(/\s+/g, ' ').trim();
  }

  /** Equation for one rule of `rw [...]`; `sigOf(name)` gives a constant's signature (may be async). */
  async function ruleEquation(rule, text, sigOf) {
    let term = rule.term.trim();
    let rev = Boolean(rule.rev);
    const show = term.match(/^\(?\s*show\s+([\s\S]+?)\s+(?:from|by)\b/);
    if (show) return ruleEquationFrom(show[1], [], {}, rev, text);
    const parts = appParts(term);
    if (!parts) return null;
    let head = parts.head;
    const { positional, named } = parts;
    if (/\.symm$/.test(head)) { rev = !rev; head = head.slice(0, -5); }
    let sig = /^[\w'Ͱ-Ͽ₀-ₜ]+$/.test(head) ? localType(head, text) : null;
    if (!sig && sigOf) sig = await sigOf(head);
    return sig ? ruleEquationFrom(sig, positional, named, rev, text) : null;
  }

  /** Does a tactic at `pos` still affect the hovered (last) line? Bullets, nesting and `by` blocks scope it. */
  function tacticInScope(text, pos, hoverStart) {
    const ls = text.lastIndexOf('\n', pos - 1) + 1;
    if (/\bby\b/.test(text.slice(ls, pos))) return false; // nested `by` on the same line: local to it
    const col = (text.slice(ls).match(/^\s*(?:·\s*)?/) || [''])[0].length;
    let p = text.indexOf('\n', pos);
    if (p === -1) return false;
    p++;
    while (p <= hoverStart && p < text.length) {
      const e = text.indexOf('\n', p);
      const line = text.slice(p, e === -1 ? text.length : e);
      if (line.trim() && (line.match(/^\s*/) || [''])[0].length < col) return false;
      if (e === -1) break;
      p = e + 1;
    }
    return true;
  }

  /**
   * Tactics before the hovered line that change hypothesis `name` after position `after`:
   * `{ kind: 'rw', rules, nth }` (rw / rwa / rewrite / erw / nth_rw), `{ kind: 'change', type }`,
   * or `{ kind: 'opaque' }` for tactics that can't be replayed from the text (simp, norm_num, …).
   */
  function hypothesisChanges(name, text, after) {
    const hoverStart = text.lastIndexOf('\n') + 1;
    const changes = [];
    const targets = (locs) => namesIn(locs.replace(/⊢/g, ' ')).includes(name) || /(^|\s)\*(\s|$)/.test(locs);
    const usable = (pos) => {
      if (pos <= after || pos >= hoverStart) return false;
      const ls = text.lastIndexOf('\n', pos - 1) + 1;
      return !/--/.test(text.slice(ls, pos)) && tacticInScope(text, pos, hoverStart);
    };
    const oneLine = (s) => s.replace(/\s+/g, ' ').trim();
    let m;
    const rwRe = /\b(rw|rwa|rewrite|erw|nth_rw|nth_rewrite)\b\s*(\d+)?\s*\[/g;
    while ((m = rwRe.exec(text)) !== null) {
      if (!usable(m.index)) continue;
      const open = m.index + m[0].length - 1;
      const close = matchClose(text, open);
      if (close === -1) continue;
      const tail = text.slice(close + 1).match(/^\s*at\s+([^\n;]*)/);
      if (!tail || !targets(tail[1].replace(/<;>.*$/, ''))) continue;
      const rules = splitTop(text.slice(open + 1, close), ',').filter(Boolean).map(r => ({
        term: r.replace(/^(←|<-)\s*/, '').trim(), rev: /^(←|<-)/.test(r)
      }));
      changes.push({ kind: 'rw', pos: m.index, rules, nth: m[2] ? parseInt(m[2], 10) : 0, text: oneLine(text.slice(m.index, close + 1) + tail[0]) });
    }
    const changeRe = /\bchange\s+([^\n]+?)\s+at\s+([^\n;]*)/g;
    while ((m = changeRe.exec(text)) !== null) {
      if (usable(m.index) && targets(m[2])) changes.push({ kind: 'change', pos: m.index, type: m[1].trim(), text: oneLine(m[0]) });
    }
    const opaqueRe = /\b(simp|simp_rw|dsimp|norm_num|push_neg|push_cast|norm_cast|field_simp|ring_nf|unfold|delta|conv|lift|zify|qify|rify|abel_nf|simp_arith|cancel_denoms|nontriviality)\b[^\n]*?\bat\s+([^\n;]*)/g;
    while ((m = opaqueRe.exec(text)) !== null) {
      if (usable(m.index) && targets(m[2])) changes.push({ kind: 'opaque', pos: m.index, text: oneLine(m[0]) });
    }
    const allRe = /\b(simp_all|subst_vars|subst)\b[^\n]*/g;
    while ((m = allRe.exec(text)) !== null) {
      if (usable(m.index)) changes.push({ kind: 'opaque', pos: m.index, text: oneLine(m[0]) });
    }
    const replaceRe = new RegExp(`\\breplace\\s+${name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\s*:=`, 'g');
    while ((m = replaceRe.exec(text)) !== null) {
      if (usable(m.index)) changes.push({ kind: 'opaque', pos: m.index, text: oneLine(text.slice(m.index, text.indexOf('\n', m.index) === -1 ? text.length : text.indexOf('\n', m.index))) });
    }
    return changes.sort((a, b) => a.pos - b.pos);
  }

  /**
   * Replay `changes` on `baseType`. `rw`-style rewrites and `change` are applied; replay stops
   * at a tactic it can't model. Resolves to { type, applied, stoppedAt?, failedAt?, failedRule? }.
   */
  async function replayChanges(baseType, changes, text, sigOf) {
    let type = baseType;
    const applied = [];
    for (const ch of changes) {
      if (ch.kind === 'change') { type = ch.type; applied.push(ch); continue; }
      if (ch.kind === 'opaque') return { type, applied, stoppedAt: ch };
      let tree = parseTerm(type);
      if (!tree) return { type, applied, failedAt: ch };
      for (const rule of ch.rules) {
        let eq = null;
        try { eq = await ruleEquation(rule, text, sigOf); } catch (err) { eq = null; }
        const next = eq && rewriteTerm(tree, eq.lhs, eq.rhs, eq.vars, ch.nth);
        if (!next) return { type, applied, failedAt: ch, failedRule: rule.term };
        tree = next;
      }
      type = showTerm(tree);
      applied.push(ch);
    }
    return { type, applied };
  }

  /** Tooltip fields for a local whose type was replayed: { typeSignature, docstring }. */
  function describeReplay(info, result) {
    const r = info.replay;
    const code = (c) => `\`${c.text.length > 80 ? c.text.slice(0, 77) + '…' : c.text}\``;
    const declared = `declared as \`${r.baseType}\``;
    const blocked = result.stoppedAt || result.failedAt;
    let type = result.type;
    let signature;
    if (r.projection) {
      const proj = blocked ? null : projectionChain(type, r.projection);
      signature = `${info.name} : ${proj ? proj.type : '_'}`;
      if (proj) type = proj.type;
    } else {
      signature = `${info.name} : ${type}`;
    }
    let doc;
    if (!blocked) {
      doc = `${r.lead} Type after ${result.applied.map(code).join(', ')}, replayed from the rewrite rules' statements (${declared}).`;
    } else {
      const why = result.stoppedAt
        ? `${code(result.stoppedAt)} changes it, and that can't be replayed without Lean`
        : `${code(result.failedAt)} changes it, but the rewrite couldn't be replayed${result.failedRule ? ` (rule \`${result.failedRule}\`)` : ''}`;
      signature += '  -- outdated';
      doc = `${r.lead} **Outdated:** ${why}. ` +
        (r.projection ? `Its base was \`${result.type}\` before that tactic.` : 'Shown is the type before that tactic') +
        (result.applied.length ? ` (after ${result.applied.map(code).join(', ')}).` : '.') + ` Originally ${declared}.`;
    }
    return { typeSignature: signature, docstring: doc };
  }

  /**
   * Base name and fields of a term used as a receiver: `(hasSum_map_coeff h m).mul_right (q ^ m)`
   * → { base: 'hasSum_map_coeff', path: ['mul_right'] }. Null when the base isn't a name.
   */
  function termChain(text) {
    let n = parseTerm(text);
    const path = [];
    for (let guard = 0; n && guard < 30; guard++) {
      n = tCore(n);
      if (n.k === 'app') { n = n.f; continue; }
      if (n.k === 'proj') { path.unshift(n.f); n = n.e; continue; }
      break;
    }
    return n && n.k === 'id' ? { base: n.v, path } : null;
  }

  // --- Hovering inside a term: the smallest term containing the position, with its type ---
  //
  // Lean's hover on the space in `f x`, on a bracket or an operator shows the innermost term
  // there with its type (`f x : β`). Here the term is parsed from the source line (joined with
  // the lines it continues) and its type inferred from local types and constants' signatures.

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
      if (GAP_NOT_TERM.test(text.slice(st.at, hi))) continue;
      for (const en of ends) {
        let a = st.at, b = en;
        const lead = text.slice(a, b).match(GAP_LEAD);
        if (lead) a += lead[0].length;
        while (a < b && /\s/.test(text[a])) a++;
        while (b > a && /\s/.test(text[b - 1])) b--;
        if (offset < a || offset >= b) continue;
        const src = text.slice(a, b);
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
      if (j > s0) text += /(^|[^\w'])by(?![\w'])/.test(lastCode) && !/[([{⟨]\s*by\b/.test(lastCode) ? ';' : ' ';
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
    '×ℂ': 'Complex.«term_×ℂ_»', "⁻¹'": "Set.«term_⁻¹'_»", "''": 'Set.image', '<|': '«term_<|_»', '|>': '«term_|>_»'
  };
  const PREFIX_DOCS = { '¬': '«term¬_»', '-': '«term-_»' };
  const POSTFIX_DOCS = { '⁻¹': '«term_⁻¹»', 'ᶜ': '«term_ᶜ»' };

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
  const TYPE_SORTS = {
    'ℕ': 'Type', 'ℤ': 'Type', 'ℚ': 'Type', 'ℝ': 'Type', 'ℂ': 'Type', 'Nat': 'Type', 'Int': 'Type', 'Rat': 'Type',
    'Real': 'Type', 'Complex': 'Type', 'Bool': 'Type', 'Prop': 'Type', 'True': 'Prop', 'False': 'Prop'
  };
  const COMP_SIG = '{α : Sort u} {β : Sort v} {δ : Sort w} (f : β → δ) (g : α → β) : α → δ';
  const LOCAL_NAME = /^[\w'Ͱ-Ͽἀ-῿₀-ₜ]+$/;

  /**
   * A term as Lean prints it after elaboration: ascriptions are gone, and a local ascribed a
   * different type is coerced (`(n : ℝ)` with `n : ℕ` prints as `↑n`).
   */
  function termDisplay(node, text) {
    return showTerm(stripAscriptions(node, text || ''));
  }

  const NUMBER_TOWER = ['ℕ', 'ℤ', 'ℚ', 'ℝ', 'ℂ'];
  const NUMBER_ALIASES = { Nat: 'ℕ', Int: 'ℤ', Rat: 'ℚ', Real: 'ℝ', Complex: 'ℂ' };
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
      try { return (await sigOf(name)) || null; } catch (err) { return null; }
    };

    // A local's current type; `undefined` when `name` isn't a local, null when it is one whose
    // type can't be told (untyped, or changed by a tactic we can't replay).
    const localSig = async (name) => {
      if (!LOCAL_NAME.test(name)) return undefined;
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
        try { r = await inferPending(info.inferNeeded, text, sigOf); } catch (err) { r = null; }
        type = r && r.typeSignature.startsWith(prefix) ? r.typeSignature.slice(prefix.length) : null;
      }
      if (!type || type === '_') return null;
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
      return fsig ? residualSignature(fsig, [], {}, text, { receiver: { term: recvText, type: recvType, binders: r.lead } }) : null;
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
          return residualSignature(fSig, positional, named, text, { argTypes });
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
            // The sort of a function type is its codomain's (`A → P : Prop` for a proposition `P`).
            const r = await typeOf(n.r);
            return r === 'Prop' || /^(Type|Sort)\b/.test(r || '') ? r : null;
          }
          if (n.op === '×') {
            const l = await typeOf(n.l);
            return /^(Type|Sort)\b/.test(l || '') ? l : null;
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
          return n.op === '-' ? typeOf(n.e) : null;
        case 'post': case 'abs': return typeOf(n.e);
        case 'norm': return 'ℝ';
        case 'bind': {
          if (['∀', '∃', '∃!'].includes(n.head)) return 'Prop';
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
    // Types of subterms keep their ascriptions (matching sees through them); only what is
    // shown at the end is printed the way Lean prints it.
    const typeOf = async (n) => displayType(await sigOfTerm(n), text, true);
    // Positional / named arguments of an application and the types used to solve variables.
    const argsOf = async (n) => {
      const positional = [];
      const named = {};
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
    return (shown && shown.includes('?') && hint.expected && solvedByExpected(sig, hint.expected)) || shown;
  }

  /** Apply anonymous projections `[1, 2, …]` to a type; null if a step isn't known. */
  function projectionChain(type, indices) {
    let t = type;
    for (const n of indices) {
      const p = projectionType(t, n);
      if (!p) return null;
      t = p.type;
    }
    return { type: t };
  }

  // --- Where the hovered line lives: repo, commit, path, line (for file-scope lookup) ---

  let revisionCache = { key: null, head: null, base: null };

  /** Head/base commit of the PR on this page, from GitHub's embedded JSON (null if absent). */
  function pageRevision() {
    const key = location.pathname.split('/').slice(0, 5).join('/');
    if (revisionCache.key === key) return revisionCache;
    let head = null;
    let base = null;
    for (const sc of document.querySelectorAll('script[type="application/json"], script[type="application/ld+json"]')) {
      const t = sc.textContent || '';
      if (!head) head = (t.match(/"head(?:Oid|Sha|RefOid)"\s*:\s*"([0-9a-f]{40})"/) || [])[1] || null;
      if (!base) base = (t.match(/"base(?:Oid|Sha|RefOid)"\s*:\s*"([0-9a-f]{40})"/) || [])[1] || null;
      if (head && base) break;
    }
    revisionCache = { key, head, base };
    return revisionCache;
  }

  function filePathFor(el) {
    const holder = el.closest('[data-file-path], [data-tagsearch-path], [data-path]');
    if (holder) {
      return holder.getAttribute('data-file-path') || holder.getAttribute('data-tagsearch-path') || holder.getAttribute('data-path');
    }
    const region = el.closest('[aria-labelledby]');
    const heading = region && document.getElementById(region.getAttribute('aria-labelledby'));
    const text = heading && heading.textContent.replace(/[\u200e\u200f]/g, '').trim();
    return text && /\.lean$/.test(text) ? text : null;
  }

  function lineFor(el) {
    const cell = el.closest('td, [role="gridcell"]');
    if (cell && cell.hasAttribute('data-line-number')) {
      return {
        line: parseInt(cell.getAttribute('data-line-number'), 10),
        side: cell.getAttribute('data-diff-side') === 'left' ? 'left' : 'right'
      };
    }
    // Classic view: line numbers live in sibling cells before the code cell.
    const row = el.closest('tr');
    if (!row || !cell) return null;
    const before = [];
    for (const c of row.children) {
      if (c === cell) break;
      if (c.hasAttribute('data-line-number')) before.push(c);
    }
    if (before.length === 0) return null;
    const deleted = rowIsDeletion(row, cell);
    const numCell = deleted ? before[0] : before[before.length - 1];
    return { line: parseInt(numCell.getAttribute('data-line-number'), 10), side: deleted ? 'left' : 'right' };
  }

  /** { owner, repo, pr, sha, side, path, line } for the hovered node on a PR page, or null. */
  function fileRefFromDom(node) {
    const el = node && (node.nodeType === 1 ? node : node.parentElement);
    if (!el || !el.closest) return null;
    const m = location.pathname.match(/^\/([^/]+)\/([^/]+)\/pull\/(\d+)/);
    if (!m) return null;
    const pos = lineFor(el);
    const path = filePathFor(el);
    if (!pos || !pos.line || !path) return null;
    const rev = pageRevision();
    return {
      owner: m[1], repo: m[2], pr: m[3],
      sha: pos.side === 'left' ? rev.base : rev.head,
      side: pos.side, path, line: pos.line
    };
  }

  // `self` lets the service worker importScripts() this file for `variable` lookups.
  (typeof window !== 'undefined' ? window : self).VersoBinderContext = {
    findBinderType,
    findUntypedBinder,
    localVariableInfo,
    localType,
    inferLocalType,
    formatInferred,
    parsePattern,
    destructure,
    peelGoal,
    elementTypeOf,
    replaceWord,
    conclusionOf,
    codomainOf,
    splitApp,
    structureBeingBuilt,
    namedArgFunction,
    namedArgInfo,
    projectionType,
    projectionInfo,
    laterChanges,
    parseTerm,
    showTerm,
    matchTerm,
    rewriteTerm,
    peelSignature,
    ruleEquation,
    hypothesisChanges,
    replayChanges,
    describeReplay,
    inferPending,
    applicationTypeFrom,
    applyArgs,
    residualSignature,
    displayType,
    leanSignature,
    termAtOffset,
    termTypeOf,
    termDisplay,
    notationDocName,
    joinStatement,
    statementAround,
    receiverResultType,
    termChain,
    parenReceiver,
    applicationHead,
    typeHead,
    inferReceiverNamespace,
    declarationContext,
    contextFromDom,
    fileRefFromDom,
    pageRevision
  };
})();
