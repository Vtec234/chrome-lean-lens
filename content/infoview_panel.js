/**
 * Lean's infoview in a panel at the right of a pull request's page, when the local helper is
 * in use: the goals and messages at a cursor, as an editor shows them beside the file.
 *
 * The panel holds an extension page (infoview/host.html), which talks to the helper and shows
 * the infoview. This script is the part on GitHub's page: the tab that opens and hides the
 * panel, its width, and the cursor. A click in the Lean code is where the cursor goes, as a
 * click in an editor would put it: the panel is told the file, line and column, and the place
 * is marked in the code.
 */
(function () {
  const STATE_KEY = 'lean_lens_infoview_panel';
  const MIN_WIDTH = 280;
  const DEFAULT_WIDTH = 440;

  /**
   * The position a click in the code means: `{ref, line, character, container, offset}` with
   * `ref` the file and line as the hovers read them, `line` and `character` counted from 0 as
   * Lean's server counts (UTF-16 units, as the browser counts a line's text); or null when the
   * click is not in a line of a Lean file.
   */
  function cursorAt(event) {
    const tk = window.LeanTokenizer;
    const ctx = window.VersoBinderContext;
    if (!tk || !ctx || !tk.caretFromEvent || !tk.isInsideLeanContext(event.target)) return null;
    const caret = tk.caretFromEvent(event);
    if (!caret) return null;
    const ref = ctx.fileRefFromDom(caret.textNode);
    if (!ref || !ref.line || !/\.lean$/.test(ref.path || '')) return null;
    const marker = tk.markerLength(caret.container);
    const length = (caret.container.textContent || '').length;
    const offset = Math.max(marker, Math.min(caret.offset, length));
    return { ref, line: ref.line - 1, character: offset - marker, container: caret.container, offset, length };
  }

  /** Whether the page is a dark one, from the color behind its text. */
  function pageTheme() {
    const channels = (getComputedStyle(document.body).backgroundColor.match(/[\d.]+/g) || []).map(Number);
    if (channels.length < 3 || channels[3] === 0) return 'light';
    return 0.2126 * channels[0] + 0.7152 * channels[1] + 0.0722 * channels[2] < 128 ? 'dark' : 'light';
  }

  const send = (message) => new Promise((resolve) => {
    try {
      chrome.runtime.sendMessage(message, (res) => resolve(chrome.runtime.lastError ? null : res));
    } catch (err) {
      resolve(null);
    }
  });

  class InfoviewPanel {
    constructor() {
      this.root = null;
      this.frame = null;
      this.port = null;
      this.open = false;
      this.width = DEFAULT_WIDTH;
      this.page = null;
      this.sent = '';
      this.restored = false;
      this.enabled = false;
      this.commits = new Map(); // pull request → its commit, asked of GitHub when the page does not say
      this.onClick = (event) => this.clicked(event);
    }

    /**
     * What the page shows, for the panel: `{repo, sha, pr, current, files}` on a pull request
     * with Lean files, else null. `sha` may be missing when the page does not name its commit.
     */
    pageInfo() {
      const ctx = window.VersoBinderContext;
      const scanner = window.LeanPRScanner;
      const pr = location.pathname.match(/^\/([^/]+)\/([^/]+)\/pull\/(\d+)/);
      if (!pr || !ctx || !scanner) return null;
      const files = scanner.filePaths();
      if (!files.length) return null;
      // (The outline knows which file is in the middle of the window.)
      const outline = window.LeanOutlinePanel;
      let inView = null;
      try { inView = outline ? outline.fileInView(files.map((path) => ({ path }))) : null; } catch (err) { inView = null; }
      const key = `${pr[1]}/${pr[2]}#${pr[3]}`;
      const sha = ctx.pageRevision().head || this.commits.get(key) || null;
      if (!sha && !this.commits.has(key)) {
        // The page does not name its commit: GitHub is asked, once, and the panel told then.
        this.commits.set(key, null);
        send({ action: 'PAGE_COMMIT', fileRef: { owner: pr[1], repo: pr[2], pr: pr[3], side: 'right' } }).then((res) => {
          if (!res || !res.sha) return;
          this.commits.set(key, res.sha);
          this.refresh(this.enabled);
        });
      }
      return {
        owner: pr[1], name: pr[2], repo: `${pr[1]}/${pr[2]}`, pr: pr[3], sha,
        files, current: inView && files.includes(inView.path) ? inView.path : files[0]
      };
    }

    /** Show the tab when the helper is in use and the page has Lean files; hide it otherwise. */
    refresh(enabled) {
      this.enabled = Boolean(enabled);
      let page = enabled ? this.pageInfo() : null;
      // A long pull request's page holds only the files near the window. While it stays on the
      // same pull request, what was known of it stays: Lean is not stopped by scrolling past
      // the Lean files.
      const on = location.pathname.match(/^\/([^/]+)\/([^/]+)\/pull\/(\d+)/);
      const known = this.page;
      if (enabled && !page && known && on && known.owner === on[1] && known.name === on[2] && known.pr === on[3]) page = known;
      this.page = page;
      if (!page) {
        if (this.root) this.root.classList.add('lean-infoview-gone');
        this.shift(false);
        this.tell();
        return;
      }
      this.ensureDom();
      this.root.classList.remove('lean-infoview-gone');
      this.shift(this.open);
      if (!this.restored) {
        // As it was left on the last page: open or hidden, and how wide.
        this.restored = true;
        try {
          chrome.storage.local.get([STATE_KEY], (res) => {
            const kept = res && res[STATE_KEY];
            if (!kept) return;
            if (Number(kept.width) >= MIN_WIDTH) this.setWidth(Number(kept.width));
            if (kept.open && this.page) this.setOpen(true, false);
          });
        } catch (err) { /* starts hidden */ }
      }
      this.tell();
    }

    ensureDom() {
      if (this.root && document.body.contains(this.root)) return;
      this.root = document.createElement('div');
      this.root.className = 'lean-infoview lean-infoview-closed';
      this.root.innerHTML = `
        <button class="lean-infoview-tab" title="Show Lean's infoview: goals and messages at the place you click (Lean Lens)">Infoview</button>
        <div class="lean-infoview-panel" role="complementary" aria-label="Lean infoview">
          <div class="lean-infoview-grip" title="Drag to resize"></div>
          <div class="lean-infoview-head">
            <span class="lean-infoview-title">Lean infoview</span>
            <span class="lean-infoview-note"></span>
            <button class="lean-infoview-hide" title="Hide the infoview (Lean keeps running)">⟩</button>
          </div>
          <div class="lean-infoview-body"></div>
        </div>`;
      document.body.appendChild(this.root);
      this.root.querySelector('.lean-infoview-tab').addEventListener('click', () => this.setOpen(true));
      this.root.querySelector('.lean-infoview-hide').addEventListener('click', () => this.setOpen(false));
      // The tooltip's hovers stay out of the panel.
      this.root.addEventListener('mousemove', (e) => e.stopPropagation());
      this.bindGrip(this.root.querySelector('.lean-infoview-grip'));
      this.setWidth(this.width);
    }

    bindGrip(grip) {
      let from = null;
      grip.addEventListener('pointerdown', (e) => {
        from = { x: e.clientX, width: this.width };
        grip.setPointerCapture(e.pointerId);
        this.root.classList.add('lean-infoview-resizing');
        e.preventDefault();
      });
      grip.addEventListener('pointermove', (e) => { if (from) this.setWidth(from.width + from.x - e.clientX); });
      const done = () => {
        if (!from) return;
        from = null;
        this.root.classList.remove('lean-infoview-resizing');
        this.save();
      };
      grip.addEventListener('pointerup', done);
      grip.addEventListener('pointercancel', done);
    }

    setWidth(width) {
      this.width = Math.round(Math.max(MIN_WIDTH, Math.min(width, Math.max(MIN_WIDTH, window.innerWidth * 0.7))));
      if (this.root) this.root.style.setProperty('--lean-infoview-width', `${this.width}px`);
      if (this.open) this.shift(true);
    }

    /** Make room for the panel beside the page, or give it back. */
    shift(on) {
      const html = document.documentElement;
      html.classList.toggle('lean-infoview-open', Boolean(on));
      if (on) html.style.setProperty('--lean-infoview-width', `${this.width}px`);
      else html.style.removeProperty('--lean-infoview-width');
    }

    save() {
      try { chrome.storage.local.set({ [STATE_KEY]: { open: this.open, width: this.width } }); } catch (err) { /* not kept */ }
    }

    setOpen(open, remember = true) {
      if (!this.root) return;
      this.open = open;
      this.root.classList.toggle('lean-infoview-closed', !open);
      this.shift(open && !this.root.classList.contains('lean-infoview-gone'));
      if (open) {
        this.ensureFrame();
        document.addEventListener('click', this.onClick, true);
      } else {
        document.removeEventListener('click', this.onClick, true);
      }
      if (remember) this.save();
    }

    /** The extension's page in the panel, made the first time the panel opens. */
    ensureFrame() {
      if (this.frame && this.root.contains(this.frame)) return;
      const id = Array.from(crypto.getRandomValues(new Uint8Array(12)), (b) => b.toString(16).padStart(2, '0')).join('');
      const frame = document.createElement('iframe');
      frame.className = 'lean-infoview-frame';
      frame.title = 'Lean infoview';
      // Once the page there has loaded it is handed one end of a message channel, which the
      // two then talk over. The page takes it only with the key the extension's background
      // gave out for this frame: scripts of the page on GitHub can post to the frame too, but
      // cannot ask the background for anything.
      const key = send({ action: 'INFOVIEW_KEY', id });
      frame.addEventListener('load', async () => {
        const answer = await key;
        if (this.frame !== frame || !answer || !answer.key || !frame.contentWindow) return;
        const channel = new MessageChannel();
        channel.port1.onmessage = (event) => this.fromHost(event.data);
        // (Delivered only if the frame still shows the extension's page.)
        frame.contentWindow.postMessage({ leanLens: 'infoview-panel', key: answer.key }, new URL(chrome.runtime.getURL('')).origin, [channel.port2]);
        if (this.port) this.port.close();
        this.port = channel.port1;
        this.sent = '';
        this.port.postMessage({ type: 'theme', theme: pageTheme() });
        this.tell();
      });
      frame.src = `${chrome.runtime.getURL('infoview/host.html')}#${id}`;
      this.root.querySelector('.lean-infoview-body').appendChild(frame);
      this.frame = frame;
    }

    /** Tell the panel what the page shows (again when it changes). */
    tell() {
      if (!this.port) return;
      const page = this.page;
      const said = page ? { repo: page.repo, sha: page.sha, pr: page.pr, current: page.current } : null;
      const key = JSON.stringify(said);
      if (key === this.sent) return;
      this.sent = key;
      this.port.postMessage({ type: 'theme', theme: pageTheme() });
      this.port.postMessage({ type: 'page', page: said });
    }

    /** A click on the page while the panel is open: in Lean code, it moves the infoview's cursor. */
    clicked(event) {
      if (!this.open || !this.port || !this.page || event.button !== 0) return;
      if (this.root.contains(event.target) || (event.target.closest && event.target.closest('#verso-hover-root, .lean-outline'))) return;
      let at = null;
      try { at = cursorAt(event); } catch (err) { at = null; }
      if (!at) return;
      const note = this.root.querySelector('.lean-infoview-note');
      if (at.ref.side === 'left') {
        // A removed line is the base commit's: Lean runs on the pull request's.
        note.textContent = 'That line is not in the pull request’s version';
        return;
      }
      const sha = at.ref.sha || this.page.sha;
      if (!sha) return;
      note.textContent = '';
      // (For whoever looks at the page's elements: where the cursor is.)
      this.root.dataset.cursor = `${at.ref.path}:${at.line + 1}:${at.character}`;
      this.mark(at);
      this.port.postMessage({
        type: 'cursor',
        cursor: { repo: `${at.ref.owner}/${at.ref.repo}`, sha, pr: at.ref.pr, path: at.ref.path, line: at.line, character: at.character }
      });
    }

    /** Mark the cursor in the code: the character it is before (at a line's end, the one before it). */
    mark(at) {
      if (typeof CSS === 'undefined' || !CSS.highlights || typeof Highlight === 'undefined') return;
      const tk = window.LeanTokenizer;
      const start = at.offset < at.length ? at.offset : at.offset - 1;
      const range = start >= 0 ? tk.rangeForOffsets(at.container, start, start + 1) : null;
      if (range) CSS.highlights.set('lean-lens-cursor', new Highlight(range));
      else CSS.highlights.delete('lean-lens-cursor');
    }

    fromHost(message) {
      if (!message || message.type !== 'reveal' || !this.page || message.repo !== this.page.repo) return;
      const outline = window.LeanOutlinePanel;
      const line = Number(message.line);
      if (!outline || !outline.reveal || !Number.isInteger(line) || line < 1 || typeof message.path !== 'string') return;
      outline.reveal({ owner: this.page.owner, repo: this.page.name, pr: this.page.pr, path: message.path }, line, this.page.sha);
    }
  }

  window.LeanInfoviewPanel = new InfoviewPanel();
  window.LeanInfoviewPanel.cursorAt = cursorAt;
})();
