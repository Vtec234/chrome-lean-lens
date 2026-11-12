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

  /** A declaration's signature as Lean's hover prints it (`foo (x : ℝ) : P`); aliases as written. */
  function leanStyle(kind, name, body) {
    const bc = (typeof window !== 'undefined' ? window : self).VersoBinderContext;
    if (kind === 'alias' || !bc || !bc.leanSignature) return `${kind} ${name}${body ? ' ' + body : ''}`;
    return bc.leanSignature(name, body);
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

  class LeanPRScanner {
    constructor() {
      this.declarations = new Map();
      this.isScanning = false;
      this.lastScanTime = 0;
      this.scannedFileCount = 0;
    }

    /**
     * Clear all cached PR declarations.
     */
    reset() {
      this.declarations.clear();
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

      for (let i = 0; i < rows.length; i++) {
        const row = rows[i];
        const lineText = textOf(row);

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

        const trimmed = lineText.trim();
        const match = trimmed.match(DECL_REGEX);
        if (match) {
          const kind = match[1];
          const name = match[2];
          let rest = match[3] || '';

          // Signatures often span lines: keep reading until `:=`, `where`, `|` or ` by`.
          for (let j = i + 1; j < rows.length && j <= i + 15 && signatureEnd(rest, kind === 'alias') === -1; j++) {
            rest += '\n' + textOf(rows[j]);
          }
          const sigEnd = signatureEnd(rest, kind === 'alias');
          const body = (sigEnd !== -1 ? rest.substring(0, sigEnd) : rest).replace(/\s+/g, ' ').trim();
          const signature = leanStyle(kind, name, body);

          const lineNum = this.extractLineNumber(row, i + 1);

          const declInfo = {
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
          if (shortName && !this.declarations.has(shortName)) {
            this.declarations.set(shortName, declInfo);
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
    scanSource(text, filePath) {
      const lines = text.split('\n');
      const module = filePath.replace(/\.lean$/, '').replace(/\//g, '.');
      const frames = [];
      const decls = [];
      let doc = '';
      let inDoc = false;
      let comment = 0;
      for (let i = 0; i < lines.length; i++) {
        const t = lines[i].trim();
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
        if (m) { frames.push(m[1]); doc = ''; continue; }
        if (/^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|public|private)\s+)*section\b/.test(t)) { frames.push(null); continue; }
        if (/^end\b/.test(t)) { frames.pop(); continue; }
        m = t.match(DECL_REGEX);
        if (!m) {
          if (!t.startsWith('@[')) doc = '';
          continue;
        }
        const kind = m[1];
        const declared = m[2];
        let rest = m[3] || '';
        for (let j = i + 1; j < lines.length && j <= i + 15 && signatureEnd(rest, kind === 'alias') === -1; j++) rest += '\n' + lines[j];
        const sigEnd = signatureEnd(rest, kind === 'alias');
        const body = (sigEnd !== -1 ? rest.substring(0, sigEnd) : rest).replace(/\s+/g, ' ').trim();
        const ns = frames.filter(Boolean).join('.');
        const name = declared.startsWith('_root_.') ? declared.slice(7) : (ns ? `${ns}.${declared}` : declared);
        decls.push({
          name, declaredAs: declared, shortName: declared.split('.').pop(), kind,
          typeSignature: leanStyle(kind, name, body), signature: body,
          docstring: doc, module, filePath, lineNumber: i + 1, source: 'project'
        });
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
          if (existing && existing.element) continue;
          this.declarations.set(k, d);
        }
        if (d.shortName && !this.declarations.has(d.shortName)) this.declarations.set(d.shortName, d);
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
