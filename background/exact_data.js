/**
 * Reading the data the Lean Lens helper produces (helper/convert.mjs): what Lean itself says
 * about each token of a file, and the proof state at each tactic.
 *
 * Lines are 1-based; columns are 0-based UTF-16 offsets, as the browser counts a line's text.
 */
(function (scope) {
  const FORMAT_VERSION = 2;

  const before = (l1, c1, l2, c2) => l1 < l2 || (l1 === l2 && c1 < c2);
  /** Whether (line, column) is inside the region `[l0, c0, l1, c1)`. */
  const inside = (region, line, column) =>
    !before(line, column, region[0], region[1]) && before(line, column, region[2], region[3]);

  /**
   * The token Lean knows something about at a position: `{hover, start, end}` or null.
   * `column`…`endColumn` is the hovered text; `caret` is where the pointer is in it. A caret at
   * a token's right edge still means that token.
   */
  function tokenAt(data, line, column, endColumn, caret) {
    const row = data.lines && data.lines[line];
    if (!row) return null;
    const at = (c) => {
      for (let i = 0; i < row.length; i += 3) {
        if (row[i] <= c && c < row[i + 1]) return { hover: data.hovers[row[i + 2]], start: row[i], end: row[i + 1] };
      }
      return null;
    };
    const point = typeof caret === 'number' ? caret : column;
    const hit = at(point) || (point > 0 ? at(point - 1) : null);
    if (hit && (endColumn === undefined || (hit.start < endColumn && hit.end > column))) return hit;
    // The pointer is over the hovered text but between tokens: the first token in that text.
    for (let i = 0; i < row.length; i += 3) {
      if (endColumn !== undefined && row[i] < endColumn && row[i + 1] > column) {
        return { hover: data.hovers[row[i + 2]], start: row[i], end: row[i + 1] };
      }
    }
    return null;
  }

  const goalText = (data, goal) => data.goals[goal].map((i) => data.strings[i]).join('\n');

  const startsBefore = (a, b) => before(a[0], a[1], b[0], b[1]);
  /** Whether region `outer` contains region `inner` (and is not the same region). */
  const contains = (outer, inner) => outer !== inner &&
    !startsBefore(inner, outer) && !before(outer[2], outer[3], inner[2], inner[3]) &&
    (startsBefore(outer, inner) || before(inner[2], inner[3], outer[2], outer[3]));

  /**
   * How the recorded tactics nest, worked out once per file: for each tactic, the innermost
   * tactic containing it (`parent`, -1 at the top), and the proof it belongs to (`proof`: the
   * index of the top-level `by` it follows, -1 when none does).
   */
  const structures = new WeakMap();
  function structureOf(data) {
    let s = structures.get(data);
    if (s) return s;
    const tactics = data.tactics || [];
    const parent = new Array(tactics.length).fill(-1);
    const proof = new Array(tactics.length).fill(-1);
    const stack = [];
    let current = -1;
    tactics.forEach((t, i) => {
      while (stack.length && !contains(tactics[stack[stack.length - 1]], t)) stack.pop();
      parent[i] = stack.length ? stack[stack.length - 1] : -1;
      if (parent[i] === -1 && t[4] === 1 && data.strings[t[6]] === 'by') current = i;
      proof[i] = current;
      stack.push(i);
    });
    s = { parent, proof };
    structures.set(data, s);
    return s;
  }

  /** Where the last `by` keyword Lean recorded in `[from, to)` starts, or null. */
  function lastByIn(data, from, to) {
    let found = null;
    for (let line = from[0]; line <= to[0]; line++) {
      const row = data.lines && data.lines[line];
      if (!row) continue;
      for (let i = 0; i < row.length; i += 3) {
        const hover = data.hovers[row[i + 2]];
        if (!hover || hover.k !== 'doc' || hover.n !== 'by') continue;
        const at = [line, row[i]];
        if (!before(at[0], at[1], from[0], from[1]) && before(at[0], at[1], to[0], to[1])) found = at;
      }
    }
    return found;
  }

  /**
   * The goals before tactic `index`, as goal texts, or null when Lean's data doesn't say.
   * They are the goals after the tactic just before it at the same level (`rw [h₁]` follows
   * `have h₁ …`), or, for the first tactic inside another (a `rw` rule), the goals before that
   * one. The first tactic of a proof nested in a tactic (`have h : T := by simp`) has no
   * recorded state before it.
   */
  function goalsBefore(data, index, depth = 0) {
    const tactics = data.tactics || [];
    const t = tactics[index];
    if (!t || depth > 50) return null;
    const { parent, proof } = structureOf(data);
    const p = parent[index];
    // Siblings count only after the last `by` before this tactic in its parent (or proof).
    const scopeStart = p === -1 ? (proof[index] === -1 ? null : tactics[proof[index]]) : tactics[p];
    const nested = scopeStart && p !== -1 ? lastByIn(data, scopeStart, t) : null;
    let best = -1;
    for (let k = index - 1; k >= 0; k--) {
      if (parent[k] !== p || (p === -1 && proof[k] !== proof[index])) continue;
      const s = tactics[k];
      if (before(t[0], t[1], s[2], s[3])) continue; // still running when this one starts
      if (nested && before(s[0], s[1], nested[0], nested[1])) continue;
      if (best === -1 || before(tactics[best][2], tactics[best][3], s[2], s[3])) best = k;
    }
    if (best !== -1) return tactics[best][5].map((goal) => goalText(data, goal));
    if (p === -1 || nested) return null;
    const outer = tactics[p];
    return outer[4] === 1 ? outer[5].map((goal) => goalText(data, goal)) : goalsBefore(data, p, depth + 1);
  }

  /** A recorded tactic as the tooltip shows it. */
  function stepView(data, index) {
    const t = data.tactics[index];
    const at = t[4] === 1;
    return {
      at,
      tactic: data.strings[t[6]],
      goals: t[5].map((goal) => goalText(data, goal)),
      before: at ? null : goalsBefore(data, index),
      range: t.slice(0, 4),
      index
    };
  }

  /** The index of the innermost recorded tactic at a position, or -1. */
  function tacticIndexAt(data, line, column) {
    let found = -1;
    // Sorted by start, outer before inner: the last region containing the position is innermost.
    (data.tactics || []).some((tactic, i) => {
      if (before(line, column, tactic[0], tactic[1])) return true;
      if (inside(tactic, line, column)) found = i;
      return false;
    });
    return found;
  }

  /**
   * The proof state Lean recorded for the innermost tactic at a position:
   * `{at, tactic, goals, before, range, index}` (`at`: the state at that point rather than
   * after the tactic; `before`: the goals before it, when known), or null.
   */
  function tacticAt(data, line, column) {
    const index = tacticIndexAt(data, line, column);
    if (index === -1) return null;
    const view = stepView(data, index);
    const steps = proofSteps(data, index);
    return Object.assign(view, { step: steps.indices.indexOf(index), steps: steps.indices.length });
  }

  /**
   * The tactics of the proof the tactic `index` is in, in the order they run:
   * `{indices}`, each an index into `data.tactics`.
   */
  function proofSteps(data, index) {
    const { proof } = structureOf(data);
    const tactics = data.tactics || [];
    if (!tactics[index]) return { indices: [] };
    const own = proof[index];
    const indices = [];
    tactics.forEach((t, i) => { if (proof[i] === own && (own !== -1 || i === index)) indices.push(i); });
    return { indices };
  }

  /** Every step of the proof at tactic `index`, as `stepView` describes them. */
  function stepsOfProof(data, index) {
    return proofSteps(data, index).indices.map((i) => stepView(data, i));
  }

  /** Lean's messages (errors, warnings, `#check` output) covering a position. */
  function messagesAt(data, line, column) {
    return (data.messages || []).filter((m) => inside(m, line, column)).map((m) => ({ severity: m[4], text: m[5] }));
  }

  /** A token's hover as the tooltip shows it. */
  function tokenView(hover) {
    switch (hover.k) {
      case 'const':
        return { name: hover.n, kind: 'const', typeSignature: hover.s, docstring: hover.d || '', definedHere: Boolean(hover.def) };
      case 'var':
        return { name: hover.n, kind: 'variable', typeSignature: `${hover.n} : ${hover.t}`, docstring: '' };
      case 'type':
        return { name: hover.n, kind: 'term', typeSignature: `${hover.n} : ${hover.t}`, docstring: '' };
      case 'doc':
        return { name: hover.n, kind: /(^|\.)Tactic\./.test(hover.p || '') ? 'tactic' : 'syntax', typeSignature: '', docstring: hover.d || '' };
      default:
        return null;
    }
  }

  /**
   * A field in its place. Lean's hover on the `mp` of `Nat.even_add_one.mp` is `Iff.mp`'s
   * general statement, `a → b`. What it says here follows from the hovers Lean recorded for the
   * tokens before it: `Nat.even_add_one.mp {n : ℕ} : Even (n + 1) → ¬Even n`.
   * `chain` is the dotted text up to and including the hovered field, starting at `chainColumn`.
   * Returns `{ term, signature, from }` or null (no receiver, or it can't be worked out).
   */
  function fieldInPlace(data, line, hit, chain, chainColumn) {
    const terms = scope.LeanTerms;
    if (!terms || !terms.fieldChainInPlace || !chain || typeof chainColumn !== 'number') return null;
    if (hit.hover.k !== 'const' || hit.start <= chainColumn) return null;
    const row = data.lines[line] || [];
    const text = (part) => chain.slice(part.start - chainColumn, part.end - chainColumn);
    // The tokens before the hovered one: with a dot after each, they are its receiver.
    const parts = [];
    for (let at = chainColumn; at < hit.start;) {
      let part = null;
      for (let i = 0; i < row.length; i += 3) {
        if (row[i] === at) part = { start: row[i], end: row[i + 1], hover: data.hovers[row[i + 2]] };
      }
      if (!part || part.end >= hit.start || chain[part.end - chainColumn] !== '.') return null;
      parts.push(part);
      at = part.end + 1;
    }
    if (!parts.length || parts[parts.length - 1].end + 1 !== hit.start) return null;
    const first = parts[0].hover;
    const head = first.k === 'var' ? { name: first.n, type: first.t }
      : first.k === 'const' ? { name: first.n, signature: first.s } : null;
    const fields = [...parts.slice(1), hit];
    if (!head || fields.some((part) => part.hover.k !== 'const')) return null;
    const placed = terms.fieldChainInPlace(head, fields.map((part) => ({ text: text(part), name: part.hover.n, signature: part.hover.s })));
    return placed ? Object.assign(placed, { from: first.n }) : null;
  }

  /**
   * Everything Lean recorded at a position: `{token, goals, messages, lean}`, where `token` is
   * the tooltip's fields for the token there (or null) and `lean` the Lean version used.
   * With `chain` (the dotted name up to the hovered field, starting at `chainColumn`), a field
   * shows what it says in its place, above Lean's own hover for it.
   */
  function describe(data, line, column, endColumn, caret, chain, chainColumn) {
    const hit = tokenAt(data, line, column, endColumn, caret);
    const point = typeof caret === 'number' ? Math.min(Math.max(caret, column), Math.max(column, (endColumn || column + 1) - 1)) : column;
    const token = hit ? tokenView(hit.hover) : null;
    const placed = hit && token ? fieldInPlace(data, line, hit, chain, chainColumn) : null;
    if (placed) {
      const field = chain.slice(hit.start - chainColumn, hit.end - chainColumn);
      Object.assign(token, {
        display: placed.term,
        typeSignature: placed.signature,
        docstring: `Worked out from \`${placed.from}\` and Lean's hover for \`${field}\`:\n\n\`\`\`lean\n${hit.hover.s}\n\`\`\`${hit.hover.d ? `\n\n${hit.hover.d}` : ''}`
      });
    }
    return {
      token,
      goals: tacticAt(data, line, hit ? hit.start : point),
      messages: messagesAt(data, line, hit ? hit.start : point),
      lean: data.lean || null
    };
  }

  scope.LeanLensExact = { FORMAT_VERSION, tokenAt, tacticAt, tacticIndexAt, goalsBefore, stepsOfProof, messagesAt, fieldInPlace, describe };
})(typeof self !== 'undefined' ? self : globalThis);
