/**
 * What a tactic changed in the proof state, as Lean's infoview shows it: the goals after the
 * tactic with what is new in green, and the goals before it with what went away in red.
 *
 * Goals are compared by their `case` names; hypotheses by name; a hypothesis or target whose
 * type changed is compared token by token, so only the part that changed is marked.
 */
(function (scope) {
  /** A goal's text (`case x`, `a b : T` lines, `⊢ target`) as parts. */
  function parseGoal(text) {
    const lines = String(text || '').split('\n');
    const goal = { caseName: null, hyps: [], target: null, raw: text };
    let k = 0;
    if (lines[0] && /^case\s/.test(lines[0])) {
      goal.caseName = lines[0].slice(5).trim();
      k = 1;
    }
    for (; k < lines.length; k++) {
      const line = lines[k];
      if (/^⊢/.test(line)) {
        // The target is the rest of the goal (it may span lines).
        goal.target = lines.slice(k).join('\n').replace(/^⊢\s?/, '');
        break;
      }
      const colon = hypColon(line);
      if (colon === -1) {
        // A continuation of the previous hypothesis' type.
        const last = goal.hyps[goal.hyps.length - 1];
        if (last) { last.type += '\n' + line; last.line += '\n' + line; }
        continue;
      }
      goal.hyps.push({ names: line.slice(0, colon).trim().split(/\s+/), type: line.slice(colon + 1).replace(/^\s/, ''), line });
    }
    return goal;
  }

  /** Where the `:` between a hypothesis' names and its type is (names hold no spaces in them). */
  function hypColon(line) {
    const m = line.match(/^([^\s:][^:]*?)\s:(?:\s|$)/);
    if (!m || /^\s/.test(line)) return -1;
    return m[1].length + 1;
  }

  const TOKEN = /\s+|[\p{L}\p{N}_'!?.₀-₉ₐ-ₜ]+|./gu;
  const tokens = (s) => String(s).match(TOKEN) || [];

  /**
   * `a` and `b` as segments `{text, changed}`: the tokens of each not in their longest common
   * subsequence are `changed`. Whitespace never counts as a change.
   */
  function tokenDiff(a, b) {
    const x = tokens(a);
    const y = tokens(b);
    // Too long to compare token by token: the whole text changed.
    if (x.length * y.length > 250000) return { a: [{ text: a, changed: true }], b: [{ text: b, changed: true }] };
    const n = x.length;
    const m = y.length;
    const table = new Array(n + 1);
    for (let i = 0; i <= n; i++) table[i] = new Uint16Array(m + 1);
    for (let i = n - 1; i >= 0; i--) {
      for (let j = m - 1; j >= 0; j--) {
        table[i][j] = x[i] === y[j] ? table[i + 1][j + 1] + 1 : Math.max(table[i + 1][j], table[i][j + 1]);
      }
    }
    const keepA = new Array(n).fill(false);
    const keepB = new Array(m).fill(false);
    for (let i = 0, j = 0; i < n && j < m;) {
      if (x[i] === y[j]) { keepA[i] = keepB[j] = true; i++; j++; }
      else if (table[i + 1][j] >= table[i][j + 1]) i++;
      else j++;
    }
    const segments = (toks, keep) => {
      const out = [];
      toks.forEach((t, i) => {
        const changed = !keep[i] && !/^\s+$/.test(t);
        const last = out[out.length - 1];
        // Whitespace between two changed tokens is part of the change.
        if (last && (last.changed === changed || (/^\s+$/.test(t) && last.changed))) last.text += t;
        else out.push({ text: t, changed });
      });
      // Trailing whitespace of a change is not part of it.
      return out.flatMap((s) => {
        const m2 = s.changed && s.text.match(/^(.*?)(\s+)$/s);
        return m2 ? [{ text: m2[1], changed: true }, { text: m2[2], changed: false }] : [s];
      });
    };
    return { a: segments(x, keepA), b: segments(y, keepB) };
  }

  const plain = (text) => [{ text, changed: false }];
  const whole = (text) => [{ text, changed: true }];

  /**
   * One goal, diffed against the goal it is paired with on the other side (`other`, or null).
   * Returns `{status, lines: [{segments, status}]}`; status is 'same', 'changed', or `mark`
   * ('ins' for the goals after a tactic, 'del' for the goals before it) for what has no match.
   */
  function goalView(goal, other, mark) {
    if (!other) {
      const lines = [];
      if (goal.caseName !== null) lines.push({ segments: whole(`case ${goal.caseName}`), status: mark });
      goal.hyps.forEach((h) => lines.push({ segments: whole(h.line), status: mark }));
      if (goal.target !== null) lines.push({ segments: whole(`⊢ ${goal.target}`), status: mark });
      return { status: mark, lines };
    }
    const lines = [];
    let changed = false;
    if (goal.caseName !== null) lines.push({ segments: plain(`case ${goal.caseName}`), status: 'same' });
    const otherType = new Map();
    other.hyps.forEach((h) => h.names.forEach((n) => otherType.set(n, h.type)));
    for (const h of goal.hyps) {
      const known = h.names.filter((n) => otherType.has(n));
      if (!known.length) {
        lines.push({ segments: whole(h.line), status: mark });
        changed = true;
        continue;
      }
      const before = otherType.get(known[0]);
      const names = h.names.map((n, i) => ({ text: (i ? ' ' : '') + n, changed: !otherType.has(n) || otherType.get(n) !== h.type }));
      const typeSegs = before === h.type ? plain(h.type) : tokenDiff(before, h.type).b;
      const same = before === h.type && known.length === h.names.length && h.names.every((n) => otherType.get(n) === h.type);
      if (!same) changed = true;
      lines.push({ segments: [...names, { text: ' : ', changed: false }, ...typeSegs], status: same ? 'same' : 'changed' });
    }
    if (goal.target !== null) {
      if (other.target === goal.target) {
        lines.push({ segments: plain(`⊢ ${goal.target}`), status: 'same' });
      } else {
        changed = true;
        const segs = other.target === null ? whole(goal.target) : tokenDiff(other.target, goal.target).b;
        lines.push({ segments: [{ text: '⊢ ', changed: false }, ...segs], status: 'changed' });
      }
    }
    return { status: changed ? 'changed' : 'same', lines };
  }

  /** Goals paired across two states: by case name, in order (unnamed goals pair with unnamed). */
  function pairGoals(from, to) {
    const used = new Set();
    return to.map((g) => {
      const k = from.findIndex((f, i) => !used.has(i) && f.caseName === g.caseName);
      if (k === -1) return null;
      used.add(k);
      return from[k];
    });
  }

  /**
   * The goals before and after a tactic, each goal as `goalView` describes it:
   * `{after: [view], before: [view], changed}`. `changed` is false when the tactic left the
   * state as it was.
   */
  function diffStates(beforeTexts, afterTexts) {
    const before = (beforeTexts || []).map(parseGoal);
    const after = (afterTexts || []).map(parseGoal);
    const forAfter = pairGoals(before, after);
    const forBefore = pairGoals(after, before);
    const afterViews = after.map((g, i) => goalView(g, forAfter[i], 'ins'));
    const beforeViews = before.map((g, i) => goalView(g, forBefore[i], 'del'));
    const changed = afterViews.some((v) => v.status !== 'same') || beforeViews.some((v) => v.status !== 'same');
    return { after: afterViews, before: beforeViews, changed };
  }

  scope.LeanGoalDiff = { parseGoal, tokenDiff, diffStates };
})(typeof self !== 'undefined' ? self : globalThis);
