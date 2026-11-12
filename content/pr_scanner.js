/**
 * Lean 4 In-PR Declaration Scanner.
 * Parses Pull Request diffs and commit changes on GitHub to index newly defined
 * theorems, lemmas, definitions, and structures directly within the PR!
 * Supports classic diffs and the new React-based /changes PR interface.
 */

(function () {
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

      // Regex matching Lean 4 declarations:
      // (theorem|lemma|def|inductive|structure|class|abbrev|opaque|instance) name ...
      const DECL_REGEX = /^(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|public\s+|noncomputable\s+|scoped\s+|partial\s+|nonrec\s+|unsafe\s+|meta\s+)*(theorem|lemma|def|inductive|structure|class|abbrev|opaque|instance|alias)\s+([A-Za-z0-9_'.Ͱ-Ͽ⁰-₟]+)([\s\S]*)/;
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
          const SIG_END = kind === 'alias' ? /$^/ : /:=|\bwhere\b|(^|\s)by\b|^\s*\|/;
          for (let j = i + 1; j < rows.length && j <= i + 15 && !SIG_END.test(rest); j++) {
            rest += '\n' + textOf(rows[j]);
          }
          const sigEnd = rest.search(SIG_END);
          const body = (sigEnd !== -1 ? rest.substring(0, sigEnd) : rest).replace(/\s+/g, ' ').trim();
          const signature = `${kind} ${name}${body ? ' ' + body : ''}`;

          const lineNum = this.extractLineNumber(row, i + 1);

          const declInfo = {
            name: name,
            shortName: name.split('.').pop(),
            kind: kind,
            typeSignature: signature,
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

  window.LeanPRScanner = new LeanPRScanner();
})();
