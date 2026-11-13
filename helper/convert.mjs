// Turns the JSON written by SubVerso's `subverso-extract-mod` into the file Lean Lens loads:
// what Lean knows about every token of a source file, and the proof state at every tactic.
//
// SubVerso calls its JSON format an implementation detail. As a check, conversion fails unless
// the tokens rebuild the source file, so a format change gives no data rather than hovers on
// the wrong tokens. (The same check as the TeX-LEAN dashboard's converter, which this one grew
// out of.) Only whitespace may differ: SubVerso drops the blank lines between the blocks of a
// Verso document.

export const DATA_FORMAT_VERSION = 2;

const nameOf = (name) => (Array.isArray(name) ? name.join('.') : String(name));
const cleanDoc = (doc) => (doc ? doc.trim() : '') || undefined;
const tagOf = (node) => Object.entries(node)[0];

/**
 * What hovering over a token shows, or null for nothing. Brackets and separators are left out
 * even when their syntax has docs: the term around them is what a hover there is about.
 */
function describeToken(kind, content) {
  if (typeof kind === 'string') return null; // comments, strings, `unknown`
  const [tag, value] = tagOf(kind);
  switch (tag) {
    case 'const':
    case 'anonCtor': {
      const hover = { k: 'const', n: nameOf(value.name), s: value.signature, d: cleanDoc(value.docs) };
      if (value.isDef) hover.def = 1;
      return hover;
    }
    case 'var':
      return value.type ? { k: 'var', n: content, t: value.type } : null;
    case 'wildcard':
    case 'withType':
    case 'num':
      return value.type ? { k: 'type', n: content, t: value.type } : null;
    case 'keyword':
    case 'operator': {
      // `p` is the syntax the token belongs to (`Lean.Parser.Tactic.simp`): it tells a tactic.
      const doc = cleanDoc(value.docs);
      return doc ? { k: 'doc', n: content, d: doc, p: value.name ? nameOf(value.name) : undefined } : null;
    }
    case 'sort': {
      const doc = cleanDoc(value['doc?']);
      return doc ? { k: 'doc', n: content, d: doc } : null;
    }
    case 'option':
      return { k: 'doc', n: nameOf(value.name), d: cleanDoc(value.docs) };
    default:
      return null;
  }
}

/** UTF-16 offsets of every line start, and a map from UTF-8 byte offsets to UTF-16 offsets. */
function indexSource(source) {
  const lineStarts = [0];
  const utf16AtByte = [];
  let byte = 0;
  for (let i = 0; i < source.length;) {
    const code = source.codePointAt(i);
    const units = code > 0xffff ? 2 : 1;
    const bytes = code < 0x80 ? 1 : code < 0x800 ? 2 : code < 0x10000 ? 3 : 4;
    for (let b = 0; b < bytes; b++) utf16AtByte[byte + b] = i;
    byte += bytes;
    i += units;
    if (code === 10) lineStarts.push(i);
  }
  utf16AtByte[byte] = source.length;
  return { lineStarts, utf16AtByte };
}

/** 1-based line and 0-based UTF-16 column of an offset. */
function positionOf(lineStarts, offset) {
  let lo = 0;
  let hi = lineStarts.length - 1;
  while (lo < hi) {
    const mid = (lo + hi + 1) >> 1;
    if (lineStarts[mid] <= offset) lo = mid; else hi = mid - 1;
  }
  return [lo + 1, offset - lineStarts[lo]];
}

/**
 * @param {object} module Parsed `subverso-extract-mod` output.
 * @param {string} source The exact source text the module was extracted from.
 * @returns {object} `{version, hovers, lines, strings, goals, tactics, messages}`:
 *   - `lines[n]` is a flat list of `start column, end column, hover index` for line `n`
 *     (1-based lines, 0-based UTF-16 columns, as the browser counts them);
 *   - a goal is a list of indices into `strings` (its `case`, hypothesis and `⊢` lines);
 *   - a tactic is `[line, column, end line, end column, kind, goals, label]`, where kind 0
 *     means the goals after the tactic and 1 the goals at that point (`by`, `·`, `… =>`), and
 *     label is the index in `strings` of the tactic's first line;
 *   - a message is `[line, column, end line, end column, severity, text]`.
 */
export function convertModule(module, source) {
  const { data, items } = module;
  const { lineStarts, utf16AtByte } = indexSource(source);
  const at = (offset) => positionOf(lineStarts, offset);

  const hovers = [];
  const hoverIndex = new Map();
  const lines = {};
  const strings = [];
  const stringIndex = new Map();
  const goals = [];
  const goalIndex = new Map();
  const tactics = [];
  const messages = [];
  let offset = 0;

  const intern = (table, index, value, key = value) => {
    if (!index.has(key)) {
      index.set(key, table.length);
      table.push(value);
    }
    return index.get(key);
  };

  const node = (key) => {
    const found = data.code[key];
    if (!found) throw new Error(`SubVerso output has no code entry ${key}`);
    return tagOf(found);
  };
  const tokenOf = (key) => {
    const token = data.tokens[key];
    if (!token) throw new Error(`SubVerso output has no token ${key}`);
    return token;
  };

  /** The text of a piece of highlighted code (a goal's hypothesis, a message's term). */
  const textOf = (key) => {
    const [tag, value] = node(key);
    switch (tag) {
      case 'token': return tokenOf(value.tok).content;
      case 'text':
      case 'unparsed': return value.str;
      case 'seq': return value.highlights.map(textOf).join('');
      case 'span':
      case 'tactics': return textOf(value.content);
      default: return '';
    }
  };

  /** A goal as Lean's infoview prints it: consecutive hypotheses of one type share a line. */
  const goalLines = (key) => {
    const goal = data.goals[key];
    if (!goal) throw new Error(`SubVerso output has no goal ${key}`);
    const out = goal.name ? [`case ${goal.name}`] : [];
    let group = null;
    for (const hypothesis of goal.hypotheses) {
      const names = hypothesis.names.map((name) => tokenOf(name).content);
      const type = textOf(hypothesis.typeAndVal);
      if (group && group.type === type && !type.includes(':=')) {
        group.names.push(...names);
      } else {
        if (group) out.push(`${group.names.join(' ')} : ${group.type}`);
        group = { names, type };
      }
    }
    if (group) out.push(`${group.names.join(' ')} : ${group.type}`);
    out.push(`${goal.goalPrefix}${textOf(goal.conclusion)}`);
    return out;
  };
  const goalId = (key) => {
    const ids = goalLines(key).map((line) => intern(strings, stringIndex, line));
    return intern(goals, goalIndex, ids, ids.join(','));
  };

  const messageText = (key) => {
    const content = data.messageContents[key];
    if (!content) return '';
    const [tag, value] = tagOf(content);
    switch (tag) {
      case 'text': return value;
      case 'append': return value.map(messageText).join('');
      case 'term': return textOf(value);
      case 'goal': return goalLines(value).join('\n');
      default: return '';
    }
  };

  // Spans being walked that have not reached their first piece of text yet.
  const openSpans = [];

  /** Move past `text` in the source, and return where it starts there. */
  const advance = (text) => {
    let start = offset;
    if (!source.startsWith(text, offset)) {
      // Whitespace is the one thing SubVerso may add, drop or reshape.
      const body = text.trimStart();
      if (!body) return offset;
      while (start < source.length && /\s/.test(source[start])) start += 1;
      if (!source.startsWith(body, start)) {
        throw new Error(`SubVerso output does not match the source at offset ${offset}`);
      }
      text = body;
    }
    offset = start + text.length;
    for (const span of openSpans) if (span.start === null) span.start = start;
    return start;
  };

  // The goals on the `by` that opens the proof being walked. SubVerso records these same goals
  // on a `by` nested in a tactic such as `have h : T := by …`, where the real goal is `T`, so a
  // nested `by` that repeats them carries no state here.
  let openingGoals = null;
  let tacticDepth = 0;

  const walk = (key) => {
    const [tag, value] = node(key);
    switch (tag) {
      case 'token': {
        const token = tokenOf(value.tok);
        const start = advance(token.content);
        const hover = describeToken(token.kind, token.content);
        const [line, column] = at(start);
        if (hover && !/\s/.test(token.content)) {
          const id = intern(hovers, hoverIndex, hover, JSON.stringify(hover));
          (lines[line] ||= []).push(column, column + token.content.length, id);
        }
        break;
      }
      case 'text':
      case 'unparsed':
        advance(value.str);
        break;
      case 'seq':
        value.highlights.forEach(walk);
        break;
      case 'span': {
        const span = { start: null };
        openSpans.push(span);
        walk(value.content);
        openSpans.splice(openSpans.indexOf(span), 1);
        for (const [severity, message] of value.info) {
          const text = messageText(message).trim();
          if (text && span.start !== null) messages.push([...at(span.start), ...at(offset), severity, text]);
        }
        break;
      }
      case 'tactics': {
        const start = utf16AtByte[value.startPos];
        const end = utf16AtByte[value.endPos];
        if (start === undefined || end === undefined) throw new Error('SubVerso tactic range is outside the source');
        const text = source.slice(start, end);
        const ids = value.info.map(goalId);
        const isBy = text === 'by';
        const stale = isBy && tacticDepth > 0 && openingGoals !== null && ids.join(',') === openingGoals;
        if (isBy && tacticDepth === 0) openingGoals = ids.join(',');
        if (!stale) {
          const here = isBy || text === '·' || text === '.' || text.endsWith('=>');
          const firstLine = text.split('\n')[0].trimEnd();
          const label = firstLine.length > 60 ? `${firstLine.slice(0, 59)}…` : firstLine + (text.includes('\n') ? ' …' : '');
          tactics.push([...at(start), ...at(end), here ? 1 : 0, ids, intern(strings, stringIndex, label)]);
        }
        tacticDepth += 1;
        walk(value.content);
        tacticDepth -= 1;
        break;
      }
      case 'point':
        break;
      default:
        throw new Error(`Unknown SubVerso code node: ${tag}`);
    }
  };

  for (const item of items) {
    openingGoals = null;
    walk(item.code);
  }
  if (source.slice(offset).trim() !== '') {
    throw new Error(`SubVerso output covers ${offset} of ${source.length} source characters`);
  }
  tactics.sort((a, b) => a[0] - b[0] || a[1] - b[1] || b[2] - a[2] || b[3] - a[3]);
  return { version: DATA_FORMAT_VERSION, hovers, lines, strings, goals, tactics, messages };
}
