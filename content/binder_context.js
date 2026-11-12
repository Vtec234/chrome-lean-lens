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
  const BINDER_KW = new RegExp(`(?:\\bfun|λ|∀|∃|∃!|Π|∑|∏|⋃|⋂|⨆|⨅|∫|∮)\\s+(${NAME_CHARS}(?:\\s+${NAME_CHARS})*)\\s*:(?!=)`, 'g');
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
      else if (depth === 0 && (ch === ',' || ch === '↦' || text.startsWith('=>', i))) return i;
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
      return /(?:\bfun|λ|∀|∃!?|Π|∑|∏|⋃|⋂|⨆|⨅|∫|∮|\bhave\s+\S+|\blet\s+\S+)$/.test(text.slice(Math.max(0, k - 20), k + 1));
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
    let t = type.replace(/\s+/g, ' ').trim();

    // Strip redundant outer parentheses.
    while (t.startsWith('(') && matchClose(t, 0) === t.length - 1) t = t.slice(1, -1).trim();

    if (/^(∀|Π|fun\b|λ)/.test(t)) return null;
    if (t.startsWith('∃')) return 'Exists';
    if (t.startsWith('¬')) return 'Not';

    // A lambda / binder at top level runs to the end: operators after it belong to its body.
    const cut = t.search(/\s(fun\b|λ|∀|∃|Π)|=>|↦/);
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
    const binderType = findBinderType(receiver, contextText);
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
   * Declaration text around the hovered DOM node, read from the diff.
   * Skips deleted lines unless the hover itself is on a deleted line.
   */
  function contextFromDom(node) {
    const el = node && (node.nodeType === 1 ? node : node.parentElement);
    if (!el || !el.closest) return '';
    for (const sel of LINE_SELECTORS) {
      const lineEl = el.closest(sel);
      if (!lineEl) continue;
      const fileEl = lineEl.closest(FILE_SELECTORS) || document;
      const onDeletion = isDeletion(lineEl);
      const all = Array.from(fileEl.querySelectorAll(sel)).filter(l => l === lineEl || isDeletion(l) === onDeletion);
      const idx = all.indexOf(lineEl);
      if (idx === -1) continue;
      return declarationContext(all.map(l => l.textContent || ''), idx);
    }
    return contextFromRows(el);
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
    const row = el.closest(ROW_SEL);
    const cell = el.closest(CELL_SEL);
    if (!row || !cell) return '';
    const table = row.closest('table, [role="grid"], [role="table"]') || row.parentElement;
    if (!table) return '';
    const cellsOf = (r) => Array.from(r.children).filter(c => c.matches(CELL_SEL));
    const col = cellsOf(row).indexOf(cell);
    if (col === -1) return '';
    const onDeletion = rowIsDeletion(row, cell);

    const lines = [];
    let idx = -1;
    for (const r of table.querySelectorAll(ROW_SEL)) {
      if (r.closest('table, [role="grid"], [role="table"]') !== table && r !== row) continue;
      const c = cellsOf(r)[col];
      if (!c) continue;
      if (r !== row && rowIsDeletion(r, c) !== onDeletion) continue;
      if (r === row) idx = lines.length;
      lines.push(cellCodeText(c));
    }
    return idx === -1 ? '' : declarationContext(lines, idx);
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
    scan(/(?:∑|∏|⋃|⋂|⨆|⨅|∫|∮)\s+([^:,\n]*?)\s*(?:\bin\b|∈|,)/g, 'bound by a big operator / integral');
    scan(/\b(?:by_contra!?|by_contra'|contrapose!?|by_cases!?)\s+([^\s:]+)\s*$/gm, 'introduced by `by_contra` / `by_cases`');
    scan(/\{\s*([^:{}|]+?)\s*\|(?!\|)/g, 'bound in a set-builder');
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
    const defRe = /\b(?:let|set|have)\s+([^\s:=]+)\s*:=\s*([^\n]*?)(?:\bwith\b|$)/gm;
    let dm;
    while ((dm = defRe.exec(text)) !== null) {
      if (dm[1] === name) consider(dm.index, 'defined locally', dm[2].trim());
    }
    return best ? { how: best.how, value: best.value } : null;
  }

  /** Tooltip data for a local variable hovered in `contextText`, or null if it isn't one. */
  function localVariableInfo(name, contextText) {
    if (!name || name.includes('.') || !contextText) return null;
    const binder = findBinder(name, contextText);
    if (binder) {
      return {
        name, kind: 'variable', source: 'local_var',
        typeSignature: `${name} : ${binder.type}`,
        docstring: 'Local variable / hypothesis bound in this declaration.' +
          changeWarning(name, laterChanges(name, contextText, binder.pos))
      };
    }
    const untyped = findUntypedBinder(name, contextText);
    if (untyped) {
      return {
        name, kind: 'variable', source: 'local_var',
        typeSignature: untyped.value ? `${name} := ${untyped.value}` : `${name} : _`,
        docstring: `Local variable ${untyped.how}; its type isn't written in the source, so it would need Lean to elaborate.`
      };
    }
    return null;
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
    const base = findBinder(segs[0], contextText);
    if (!base) {
      const untyped = findUntypedBinder(segs[0], contextText);
      if (!untyped) return null;
      return {
        name: chain, kind: 'variable', source: 'local_var',
        typeSignature: `${chain} : _`,
        docstring: `Projection \`.${segs.slice(1).join('.')}\` of the local \`${segs[0]}\`, which is ${untyped.how}; its type isn't written in the source.`
      };
    }
    const warning = changeWarning(segs[0], laterChanges(segs[0], contextText, base.pos));
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
    conclusionOf,
    codomainOf,
    splitApp,
    structureBeingBuilt,
    namedArgFunction,
    namedArgInfo,
    projectionType,
    projectionInfo,
    laterChanges,
    parenReceiver,
    applicationHead,
    typeHead,
    inferReceiverNamespace,
    declarationContext,
    contextFromDom,
    fileRefFromDom
  };
})();
