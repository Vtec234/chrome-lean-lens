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

  /**
   * The proof state Lean recorded for the innermost tactic at a position:
   * `{at, tactic, goals}` (`at`: the state at that point rather than after the tactic), or null.
   */
  function tacticAt(data, line, column) {
    let found = null;
    // Sorted by start, outer before inner: the last region containing the position is innermost.
    for (const tactic of data.tactics || []) {
      if (before(line, column, tactic[0], tactic[1])) break;
      if (inside(tactic, line, column)) found = tactic;
    }
    if (!found) return null;
    return {
      at: found[4] === 1,
      tactic: data.strings[found[6]],
      goals: found[5].map((goal) => goalText(data, goal)),
      range: found.slice(0, 4)
    };
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

  scope.LeanLensExact = { FORMAT_VERSION, tokenAt, tacticAt, messagesAt, fieldInPlace, describe };
})(typeof self !== 'undefined' ? self : globalThis);
