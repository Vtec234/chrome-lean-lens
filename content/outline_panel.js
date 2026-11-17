/**
 * The outline of a Lean file beside a pull request's diff (or a file page): its declarations
 * with their lines, and the commands that set what they see (`namespace`, `section`, `open`,
 * `variable`, `include`, `omit`), which GitHub's own symbol list leaves out.
 *
 * A declaration opens to what is in force at it (as `#where` prints it). On a pull request,
 * the declarations it adds are marked, with hints where one might belong instead.
 */
(function () {
  const KIND_LABEL = { namespace: 'namespace', section: 'section', end: 'end', open: 'open', variable: 'variable',
    include: 'include', omit: 'omit', universe: 'universe', set_option: 'option', export: 'export', command: 'cmd' };

  const esc = (str) => String(str).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');

  /** The Lean file pages this page shows: `{owner, repo, pr?, sha, baseSha?, side, path}` each. */
  function pageFiles() {
    const ctx = window.VersoBinderContext;
    const pr = location.pathname.match(/^\/([^/]+)\/([^/]+)\/pull\/(\d+)/);
    if (pr && ctx && window.LeanPRScanner) {
      const rev = ctx.pageRevision();
      return window.LeanPRScanner.filePaths().map((path) => ({
        owner: pr[1], repo: pr[2], pr: pr[3], sha: rev.head, baseSha: rev.base, side: 'right', path
      }));
    }
    // A file page: `/owner/repo/blob/<ref>/<path>` (the ref and path are fetched as one).
    const blob = location.pathname.match(/^\/([^/]+)\/([^/]+)\/blob\/([^/]+)\/(.+\.lean)$/);
    if (blob) {
      return [{ owner: blob[1], repo: blob[2], sha: decodeURIComponent(blob[3]), side: 'right', path: decodeURIComponent(blob[4]) }];
    }
    return [];
  }

  const send = (message) => new Promise((resolve) => {
    try {
      chrome.runtime.sendMessage(message, (res) => {
        if (chrome.runtime.lastError) resolve(null);
        else resolve(res);
      });
    } catch (err) {
      resolve(null);
    }
  });

  /** The page's code element for `line` of a file (the PR's side), or null when not shown. */
  function lineElement(fileRef, line) {
    const files = document.querySelectorAll('[data-file-path], [data-tagsearch-path], [data-path]');
    const roots = Array.from(files).filter((el) =>
      [el.getAttribute('data-file-path'), el.getAttribute('data-tagsearch-path'), el.getAttribute('data-path')].includes(fileRef.path));
    for (const root of roots.length ? roots : [document]) {
      const scope = root.closest('.file, [data-details-container-group="file"], [data-component="diff-file"], [data-tag="diff-entry"]') || root;
      for (const cell of scope.querySelectorAll(`[data-line-number="${line}"]`)) {
        if (cell.getAttribute('data-diff-side') === 'left') continue;
        const row = cell.closest('tr, [role="row"]') || cell;
        return row;
      }
    }
    // A file page.
    return document.getElementById(`LC${line}`) || document.querySelector(`[data-line-number="${line}"]`);
  }

  class OutlinePanel {
    constructor() {
      this.root = null;
      this.files = [];
      this.current = null;
      this.data = null;
      this.open = false;
      this.filter = '';
      this.expanded = new Map(); // line → where text (or a promise)
    }

    /** Show the button when the page has Lean files; hide it (and the panel) otherwise. */
    refresh() {
      this.files = pageFiles();
      if (!this.files.length) {
        if (this.root) this.root.classList.add('lean-outline-gone');
        return;
      }
      this.ensureDom();
      this.root.classList.remove('lean-outline-gone');
      if (!this.current || !this.files.some((f) => f.path === this.current.path)) this.current = this.files[0];
      if (this.open) this.renderSelect();
    }

    ensureDom() {
      if (this.root && document.body.contains(this.root)) return;
      this.root = document.createElement('div');
      this.root.className = 'lean-outline';
      this.root.innerHTML = `
        <button class="lean-outline-toggle" title="Outline of this Lean file (Lean Lens)">☰ Outline</button>
        <div class="lean-outline-panel lean-outline-hidden">
          <div class="lean-outline-head">
            <select class="lean-outline-file" aria-label="File"></select>
            <button class="lean-outline-close" title="Close">✕</button>
          </div>
          <div class="lean-outline-tools">
            <input class="lean-outline-filter" type="search" placeholder="Filter names" aria-label="Filter">
            <label><input type="checkbox" class="lean-outline-decls"> Declarations only</label>
          </div>
          <div class="lean-outline-summary"></div>
          <div class="lean-outline-list" role="list"></div>
          <div class="lean-outline-foot">Read from the file at this commit. Click a declaration for what is in force there.</div>
        </div>`;
      document.body.appendChild(this.root);
      const panel = this.root.querySelector('.lean-outline-panel');
      this.root.querySelector('.lean-outline-toggle').addEventListener('click', () => this.setOpen(!this.open));
      this.root.querySelector('.lean-outline-close').addEventListener('click', () => this.setOpen(false));
      this.root.querySelector('.lean-outline-file').addEventListener('change', (e) => {
        this.current = this.files.find((f) => f.path === e.target.value) || this.files[0];
        this.expanded.clear();
        this.load();
      });
      this.root.querySelector('.lean-outline-filter').addEventListener('input', (e) => {
        this.filter = e.target.value.trim().toLowerCase();
        this.renderList();
      });
      this.root.querySelector('.lean-outline-decls').addEventListener('change', () => this.renderList());
      panel.addEventListener('click', (e) => this.onClick(e));
      // The tooltip's hovers stay out of the panel.
      panel.addEventListener('mousemove', (e) => e.stopPropagation());
    }

    setOpen(open) {
      this.open = open;
      this.root.querySelector('.lean-outline-panel').classList.toggle('lean-outline-hidden', !open);
      this.root.classList.toggle('lean-outline-is-open', open);
      if (open) {
        // The file being read: the one in view.
        const inView = this.fileInView();
        if (inView) this.current = inView;
        this.renderSelect();
        this.load();
      }
    }

    /** The page's Lean file nearest the middle of the window, or null. */
    fileInView() {
      const middle = window.innerHeight / 2;
      let best = null;
      let bestDistance = Infinity;
      for (const file of this.files) {
        for (const el of document.querySelectorAll('[data-file-path], [data-tagsearch-path], [data-path]')) {
          if (![el.getAttribute('data-file-path'), el.getAttribute('data-tagsearch-path'), el.getAttribute('data-path')].includes(file.path)) continue;
          const r = el.getBoundingClientRect();
          if (!r.height) continue;
          const distance = r.top <= middle && r.bottom >= middle ? 0 : Math.min(Math.abs(r.top - middle), Math.abs(r.bottom - middle));
          if (distance < bestDistance) { bestDistance = distance; best = file; }
        }
      }
      return best;
    }

    renderSelect() {
      const select = this.root.querySelector('.lean-outline-file');
      select.innerHTML = this.files.map((f) => `<option value="${esc(f.path)}"${this.current && f.path === this.current.path ? ' selected' : ''}>${esc(f.path)}</option>`).join('');
      select.classList.toggle('lean-outline-single', this.files.length < 2);
    }

    load() {
      const file = this.current;
      if (!file) return;
      const list = this.root.querySelector('.lean-outline-list');
      list.innerHTML = '<div class="lean-outline-note">Reading the file…</div>';
      this.data = null;
      send({ action: 'FILE_OUTLINE', fileRef: file }).then((res) => {
        if (file !== this.current) return;
        if (!res) {
          list.innerHTML = '<div class="lean-outline-note">Could not read this file.</div>';
          return;
        }
        this.data = res;
        this.renderList();
      });
    }

    renderList() {
      const list = this.root.querySelector('.lean-outline-list');
      const summary = this.root.querySelector('.lean-outline-summary');
      if (!this.data) return;
      const declsOnly = this.root.querySelector('.lean-outline-decls').checked;
      const added = new Set(this.data.added || []);
      const hints = new Map((this.data.hints || []).map((h) => [h.line, h.hints]));
      const view = window.VersoTooltipView;
      const highlight = (code) => (view ? view.highlightLean(code, { binders: true }) : esc(code));
      const decls = this.data.entries.filter((e) => e.kind === 'decl');
      const parts = [`${decls.length} declaration${decls.length === 1 ? '' : 's'}`];
      if (this.data.added) parts.push(`${added.size} added in this pull request`);
      if (hints.size) parts.push(`${hints.size} with a placement hint`);
      summary.textContent = parts.join(' · ');
      const rows = this.data.entries.filter((e) => {
        if (e.kind === 'import') return false;
        if (declsOnly && e.kind !== 'decl') return false;
        if (!this.filter) return true;
        return (e.fullName || e.name || e.text).toLowerCase().includes(this.filter);
      });
      if (!rows.length) {
        list.innerHTML = '<div class="lean-outline-note">Nothing here.</div>';
        return;
      }
      list.innerHTML = rows.map((e) => {
        const isDecl = e.kind === 'decl';
        const label = isDecl ? e.declKind : KIND_LABEL[e.kind] || e.kind;
        const body = isDecl
          ? `<span class="lean-outline-name">${esc(e.name || '(anonymous)')}</span>${e.prefixes && e.prefixes.length ? `<span class="lean-outline-prefix">${esc(e.prefixes.map((p) => `${p} in`).join(' · '))}</span>` : ''}`
          : `<code>${highlight(e.kind === 'command' ? e.text : e.text.replace(/^\S+\s*/, '') || e.text)}</code>`;
        const rowHints = hints.get(e.line) || [];
        const where = this.expanded.get(e.line);
        return `<div class="lean-outline-row lean-outline-${isDecl ? 'decl' : 'cmd'} lean-outline-k-${esc(e.kind)}" role="listitem" style="--depth:${e.depth}" data-line="${e.line}">
          <button class="lean-outline-line" data-goto="${e.line}" title="Go to line ${e.line}">${e.line}</button>
          <span class="lean-outline-kind">${esc(label)}</span>
          <span class="lean-outline-text"${isDecl ? ` data-where="${e.line}" title="What is in force here"` : ''}>${body}</span>
          ${added.has(e.line) ? '<span class="lean-outline-new" title="Added in this pull request">new</span>' : ''}
          ${rowHints.length ? `<span class="lean-outline-warn" title="${esc(rowHints.map((h) => h.text.replace(/`/g, '')).join('\n'))}">⚑</span>` : ''}
        </div>${rowHints.map((h) => `<div class="lean-outline-hint" style="--depth:${e.depth}" data-goto="${h.line}">${this.inlineCode(h.text)}</div>`).join('')}${
          typeof where === 'string' ? `<pre class="lean-outline-where" style="--depth:${e.depth}">${where ? highlight(where) : '<span class="lean-outline-note">Nothing opened, no variables: the file\'s top level.</span>'}</pre>` : ''}`;
      }).join('');
    }

    inlineCode(text) {
      return esc(text).replace(/`([^`]+)`/g, '<code>$1</code>');
    }

    onClick(e) {
      const goto = e.target.closest('[data-goto]');
      const where = e.target.closest('[data-where]');
      if (goto) {
        this.goTo(Number(goto.getAttribute('data-goto')));
      } else if (where) {
        const line = Number(where.getAttribute('data-where'));
        if (this.expanded.has(line)) {
          this.expanded.delete(line);
          this.renderList();
          return;
        }
        this.expanded.set(line, null);
        send({ action: 'DECL_WHERE', fileRef: Object.assign({}, this.current, { line }) }).then((res) => {
          if (!this.expanded.has(line)) return;
          this.expanded.set(line, res ? res.where : '');
          this.renderList();
        });
      }
    }

    /** Scroll to a line when the page shows it, else open it on GitHub. */
    goTo(line) {
      const file = this.current;
      const el = lineElement(file, line);
      if (el) {
        el.scrollIntoView({ behavior: 'smooth', block: 'center' });
        el.classList.add('verso-highlight-target');
        setTimeout(() => el.classList.remove('verso-highlight-target'), 2500);
        return;
      }
      const path = file.path.split('/').map(encodeURIComponent).join('/');
      window.open(`https://github.com/${file.owner}/${file.repo}/blob/${file.sha}/${path}#L${line}`, '_blank', 'noopener');
    }
  }

  window.LeanOutlinePanel = new OutlinePanel();
})();
