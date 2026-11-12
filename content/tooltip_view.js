/**
 * Lean Lens hover tooltip view component.
 * Renders rich, interactive, syntax-highlighted tooltips in GitHub (styled like Lean's documentation hovers).
 */

(function () {
  class VersoTooltipView {
    constructor() {
      this.container = null;
      this.isPinned = false;
      this.currentTarget = null;
      this.currentData = null;
      this.hideTimer = null;
      this.initDOM();
      this.bindEvents();
    }

    /**
     * Initialize tooltip DOM structure.
     */
    initDOM() {
      if (document.getElementById('verso-hover-root')) {
        this.container = document.getElementById('verso-hover-root');
        return;
      }

      this.container = document.createElement('div');
      this.container.id = 'verso-hover-root';
      this.container.className = 'verso-hover-container verso-hidden';
      this.container.innerHTML = `
        <div class="verso-tooltip-card">
          <div class="verso-header">
            <div class="verso-header-left">
              <span class="verso-kind-badge" id="verso-kind">def</span>
              <span class="verso-ident-title" id="verso-title"></span>
            </div>
            <div class="verso-header-actions">
              <button class="verso-action-btn" id="verso-copy-btn" title="Copy symbol name">
                <svg width="13" height="13" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><rect x="9" y="9" width="13" height="13" rx="2" ry="2"></rect><path d="M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1"></path></svg>
              </button>
              <button class="verso-action-btn" id="verso-pin-btn" title="Pin tooltip (Alt)">
                <svg width="13" height="13" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><line x1="12" y1="17" x2="12" y2="22"></line><path d="M5 17h14v-2l-3-3V5a2 2 0 0 0-2-2h-4a2 2 0 0 0-2 2v7l-3 3v2z"></path></svg>
              </button>
              <button class="verso-action-btn" id="verso-close-btn" title="Close (Esc)">
                <svg width="13" height="13" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><line x1="18" y1="6" x2="6" y2="18"></line><line x1="6" y1="6" x2="18" y2="18"></line></svg>
              </button>
            </div>
          </div>
          <div class="verso-module-bar" id="verso-module-bar">
            <span class="verso-module-name" id="verso-module"></span>
          </div>
          <div class="verso-body">
            <div class="verso-signature-container">
              <pre class="verso-code-block" id="verso-signature"></pre>
            </div>
            <div class="verso-pr-banner verso-hidden" id="verso-pr-banner">
              <div class="verso-pr-badge">✨ Defined in this PR</div>
              <button class="verso-pr-jump-btn" id="verso-pr-jump-btn">Jump to definition &rarr;</button>
            </div>
            <div class="verso-docstring" id="verso-docstring"></div>
          </div>
          <div class="verso-footer">
            <div class="verso-footer-source" id="verso-footer-source">Verso Documentation</div>
            <div class="verso-footer-links">
              <a href="#" target="_blank" rel="noopener noreferrer" class="verso-ext-link" id="verso-docs-link">Verso Docs &rarr;</a>
            </div>
          </div>
        </div>
      `;

      document.body.appendChild(this.container);
    }

    /**
     * Bind hover and interactive actions.
     */
    bindEvents() {
      // Keep tooltip visible when mouse moves over it
      this.container.addEventListener('mouseenter', () => {
        this.clearHideTimer();
      });

      this.container.addEventListener('mouseleave', () => {
        if (!this.isPinned) {
          this.scheduleHide(150);
        }
      });

      // Pin button
      const pinBtn = this.container.querySelector('#verso-pin-btn');
      pinBtn?.addEventListener('click', (e) => {
        e.stopPropagation();
        this.togglePin();
      });

      // Close button
      const closeBtn = this.container.querySelector('#verso-close-btn');
      closeBtn?.addEventListener('click', (e) => {
        e.stopPropagation();
        this.hide(true);
      });

      // Copy symbol name
      const copyBtn = this.container.querySelector('#verso-copy-btn');
      copyBtn?.addEventListener('click', (e) => {
        e.stopPropagation();
        if (this.currentData?.name) {
          navigator.clipboard.writeText(this.currentData.name);
          copyBtn.classList.add('verso-btn-success');
          setTimeout(() => copyBtn.classList.remove('verso-btn-success'), 1200);
        }
      });

      // Jump to PR definition
      const jumpBtn = this.container.querySelector('#verso-pr-jump-btn');
      jumpBtn?.addEventListener('click', (e) => {
        e.stopPropagation();
        if (this.currentData?.element) {
          this.currentData.element.scrollIntoView({ behavior: 'smooth', block: 'center' });
          this.currentData.element.classList.add('verso-highlight-target');
          setTimeout(() => {
            this.currentData.element.classList.remove('verso-highlight-target');
          }, 2500);
        }
      });

      // Keyboard handler (Esc to dismiss, Alt to toggle pin)
      window.addEventListener('keydown', (e) => {
        if (e.key === 'Escape' && this.isVisible()) {
          this.hide(true);
        } else if (e.key === 'Alt' && this.isVisible()) {
          this.togglePin();
        }
      });
    }

    /**
     * Shade the code a hover is about, like the editor's hover highlight in Lean's VS Code
     * extension, with the CSS Custom Highlight API (no extra elements; follows scrolling).
     */
    setShade(ranges) {
      try {
        if (typeof CSS === 'undefined' || !CSS.highlights || typeof Highlight === 'undefined') return;
        if (ranges && ranges.length) CSS.highlights.set('lean-lens-hover', new Highlight(...ranges));
        else CSS.highlights.delete('lean-lens-hover');
      } catch (err) {
        // Not supported here: the tooltip alone still works.
      }
    }

    /**
     * Show definition in tooltip anchored at boundingRect, shading `shade` (ranges) in the code.
     */
    show(data, boundingRect, shade) {
      this.clearHideTimer();
      this.currentData = data;
      this.setShade(shade);

      const titleEl = this.container.querySelector('#verso-title');
      const kindEl = this.container.querySelector('#verso-kind');
      const modEl = this.container.querySelector('#verso-module');
      const sigEl = this.container.querySelector('#verso-signature');
      const docEl = this.container.querySelector('#verso-docstring');
      const prBanner = this.container.querySelector('#verso-pr-banner');
      const sourceEl = this.container.querySelector('#verso-footer-source');
      const docsLink = this.container.querySelector('#verso-docs-link');

      // Populate Name & Kind (a term's text is already in its signature line)
      titleEl.textContent = data.kind === 'term' ? '' : (data.name || 'Unknown');
      const kind = (data.kind || 'def').toLowerCase();
      kindEl.textContent = kind;
      kindEl.className = `verso-kind-badge verso-kind-${kind}`;

      // Module
      if (data.module) {
        modEl.textContent = data.module;
        modEl.parentElement.classList.remove('verso-hidden');
      } else {
        modEl.parentElement.classList.add('verso-hidden');
      }

      // Type Signature with Lean syntax highlighting
      // A term's brackets are lists / sets, not binders: don't colour them as such.
      sigEl.innerHTML = this.highlightLean(data.typeSignature || `${kind} ${data.name}`, { binders: kind !== 'term' });

      // PR Diff Banner
      if (data.source === 'pr_diff' && data.element) {
        prBanner.classList.remove('verso-hidden');
        const jumpBtn = prBanner.querySelector('#verso-pr-jump-btn');
        if (jumpBtn) {
          jumpBtn.textContent = `Jump to line ${data.lineNumber || ''} in PR →`;
        }
      } else {
        prBanner.classList.add('verso-hidden');
      }

      // Docstring (a term's hover is just its type, as in Lean)
      if (data.docstring) {
        docEl.innerHTML = this.renderMarkdown(data.docstring);
        docEl.classList.remove('verso-hidden');
      } else if (data.kind === 'term') {
        docEl.innerHTML = '';
        docEl.classList.add('verso-hidden');
      } else {
        docEl.innerHTML = '<span class="verso-no-doc">No docstring available.</span>';
        docEl.classList.remove('verso-hidden');
      }

      // Source & Docs Link
      if (data.source === 'pr_diff') {
        sourceEl.textContent = `PR Local Definition (${data.filePath || 'diff'})`;
        docsLink.classList.add('verso-hidden');
      } else if (data.source === 'builtin') {
        sourceEl.textContent = `Lean 4 Standard Library & Tactics`;
        docsLink.href = data.sourceUrl || `https://leanprover-community.github.io/mathlib4_docs/`;
        docsLink.textContent = `Mathlib Docs →`;
        docsLink.classList.remove('verso-hidden');
      } else if (data.source === 'project') {
        // Read from the repository at the PR's commit (a collapsed diff, or an imported project file).
        sourceEl.textContent = `${data.inPR ? 'Changed in this PR · ' : ''}${data.filePath}:${data.lineNumber}`;
        if (data.repo && data.sha) {
          docsLink.href = `https://github.com/${data.repo}/blob/${data.sha}/${data.filePath}#L${data.lineNumber}`;
          docsLink.textContent = 'View source →';
          docsLink.classList.remove('verso-hidden');
        } else {
          docsLink.classList.add('verso-hidden');
        }
      } else if (data.source === 'term') {
        sourceEl.textContent = 'Type inferred from the source';
        docsLink.classList.add('verso-hidden');
      } else if (data.source === 'local_var') {
        sourceEl.textContent = data.declaredAt ? `Declared with \`variable\` (line ${data.declaredAt})` : 'Local variable';
        docsLink.classList.add('verso-hidden');
      } else if (data.source === 'local_verso') {
        sourceEl.textContent = `Local companion server`;
        docsLink.href = data.sourceUrl || '#';
        docsLink.textContent = `Open source →`;
        docsLink.classList.remove('verso-hidden');
      } else {
        sourceEl.textContent = `Loogle / Mathlib docs`;
        docsLink.href = data.sourceUrl || `https://leanprover-community.github.io/mathlib4_docs/`;
        docsLink.textContent = `Mathlib Docs →`;
        docsLink.classList.remove('verso-hidden');
      }

      // Position tooltip near hovered element
      this.positionTooltip(boundingRect);

      this.container.classList.remove('verso-hidden');
      this.container.classList.add('verso-visible');
    }

    /**
     * Show a lightweight loading indicator at the hovered token.
     */
    showLoading(token, boundingRect, shade) {
      this.clearHideTimer();
      this.setShade(shade);
      const titleEl = this.container.querySelector('#verso-title');
      const kindEl = this.container.querySelector('#verso-kind');
      const sigEl = this.container.querySelector('#verso-signature');
      const docEl = this.container.querySelector('#verso-docstring');
      const prBanner = this.container.querySelector('#verso-pr-banner');
      const docsLink = this.container.querySelector('#verso-docs-link');

      titleEl.textContent = token;
      kindEl.textContent = '...';
      kindEl.className = 'verso-kind-badge';
      sigEl.innerHTML = '<span class="verso-loading-spinner"></span> Resolving definition via Verso & Loogle...';
      docEl.innerHTML = '';
      prBanner.classList.add('verso-hidden');
      docsLink.classList.add('verso-hidden');

      this.positionTooltip(boundingRect);
      this.container.classList.remove('verso-hidden');
      this.container.classList.add('verso-visible');
    }

    /**
     * Calculate optimal position for tooltip avoiding viewport boundaries and cursor overlap.
     */
    positionTooltip(rect) {
      if (!rect) return;
      const card = this.container.querySelector('.verso-tooltip-card');
      const cardWidth = 440;
      const cardHeight = Math.min(card ? card.offsetHeight || 280 : 280, 480);
      const viewportWidth = window.innerWidth;
      const viewportHeight = window.innerHeight;

      const margin = 12;
      const verticalGap = 10;
      let left = rect.left;
      let top = rect.bottom + verticalGap; // Default: place below token

      // Check vertical clearance:
      // If placing below overflows viewport bottom
      if (top + cardHeight > viewportHeight - margin) {
        // Check if there is enough space above the token
        if (rect.top - cardHeight - verticalGap >= margin) {
          top = rect.top - cardHeight - verticalGap;
        } else {
          // If neither above nor below fits cleanly, place below with clearance
          top = Math.max(margin, rect.bottom + verticalGap);
        }
      }

      // Check horizontal clearance:
      if (left + cardWidth > viewportWidth - margin) {
        left = viewportWidth - cardWidth - margin;
      }
      if (left < margin) {
        left = margin;
      }

      this.container.style.left = `${Math.round(left)}px`;
      this.container.style.top = `${Math.round(top)}px`;
    }

    /**
     * Toggle pinned state.
     */
    togglePin() {
      this.isPinned = !this.isPinned;
      const pinBtn = this.container.querySelector('#verso-pin-btn');
      if (this.isPinned) {
        pinBtn?.classList.add('verso-btn-active');
        this.container.classList.add('verso-pinned');
      } else {
        pinBtn?.classList.remove('verso-btn-active');
        this.container.classList.remove('verso-pinned');
      }
    }

    /**
     * Schedule closing the tooltip with debounce.
     */
    scheduleHide(delay = 200) {
      if (this.isPinned) return;
      this.clearHideTimer();
      this.hideTimer = setTimeout(() => {
        this.hide(false);
      }, delay);
    }

    /**
     * Clear scheduled hide timer.
     */
    clearHideTimer() {
      if (this.hideTimer) {
        clearTimeout(this.hideTimer);
        this.hideTimer = null;
      }
    }

    /**
     * Immediately hide tooltip.
     */
    hide(force = false) {
      if (this.isPinned && !force) return;
      this.clearHideTimer();
      this.setShade(null);
      this.isPinned = false;
      const pinBtn = this.container.querySelector('#verso-pin-btn');
      pinBtn?.classList.remove('verso-btn-active');
      this.container.classList.remove('verso-pinned');
      this.container.classList.remove('verso-visible');
      this.container.classList.add('verso-hidden');
    }

    /**
     * Check if currently visible.
     */
    isVisible() {
      return this.container && !this.container.classList.contains('verso-hidden');
    }

    /**
     * Single-pass syntax highlighter for Lean 4 signatures.
     * Prevents regex corruption of injected HTML tags.
     */
    highlightLean(code, opts = {}) {
      if (!code) return '';
      const binders = opts.binders !== false;

      function escapeHtml(str) {
        return str
          .replace(/&/g, '&amp;')
          .replace(/</g, '&lt;')
          .replace(/>/g, '&gt;');
      }

      // Regex matching distinct Lean token types in priority order:
      // 1. Comments: -- ... or /- ... -/
      // 2. Strings: "..."
      // 3. Keywords: def, theorem, lemma, etc.
      // 4. Typeclass Instance Binders: [...]
      // 5. Implicit Binders: {...}
      // 6. Symbols & Operators: :=, →, ∀, ∃, etc.
      const tokenRegex = /(--[^\n]*|\/-[\s\S]*?-\/)|("(?:\\[\s\S]|[^"\\])*")|(\b(?:def|theorem|lemma|axiom|inductive|structure|class|instance|where|by|have|let|suffices|show|fun|match|with|if|then|else)\b)|(\[[^\]]+\])|(\{[^}]+\})|(:=|→|∀|∃|∧|∨|¬|↔|≤|≥|=|≠|∈|⊆|∪|∩|:)/g;

      let result = '';
      let lastIndex = 0;
      let match;

      while ((match = tokenRegex.exec(code)) !== null) {
        // Append any text between matched tokens (escaped)
        if (match.index > lastIndex) {
          result += escapeHtml(code.slice(lastIndex, match.index));
        }

        const [full, comment, str, kw, inst, implicit, sym] = match;

        if (comment) {
          result += `<span class="v-comment">${escapeHtml(comment)}</span>`;
        } else if (str) {
          result += `<span class="v-str">${escapeHtml(str)}</span>`;
        } else if (kw) {
          result += `<span class="v-kw">${escapeHtml(kw)}</span>`;
        } else if (inst || implicit) {
          if (binders) {
            result += `<span class="${inst ? 'v-inst' : 'v-implicit'}">${escapeHtml(full)}</span>`;
          } else {
            // Highlight inside the brackets as ordinary code.
            result += full[0] + this.highlightLean(full.slice(1, -1), { binders: false }) + full[full.length - 1];
          }
        } else if (sym) {
          result += `<span class="v-sym">${escapeHtml(sym)}</span>`;
        }

        lastIndex = tokenRegex.lastIndex;
      }

      if (lastIndex < code.length) {
        result += escapeHtml(code.slice(lastIndex));
      }

      return result;
    }

    /**
     * Markdown renderer for docstrings. Code (fenced blocks, inline spans) is set aside first,
     * so `a * b` is not emphasis; lists (also indented, as in Lean's notation docs) come before
     * emphasis, so `* item` is not either.
     */
    renderMarkdown(text) {
      if (!text) return '';
      const esc = (str) => str.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
      const kept = [];
      const keep = (html) => `\u0000${kept.push(html) - 1}\u0000`;
      let src = text.replace(/```(?:lean)?[ \t]*\n?([\s\S]*?)```/g,
        (m, code) => `\n\n${keep(`<pre class="verso-code-block">${this.highlightLean(code.replace(/\s+$/, ''))}</pre>`)}\n\n`);
      src = src.replace(/`([^`\n]+)`/g, (m, code) => keep(`<code class="verso-inline-code">${esc(code)}</code>`));
      let html = esc(src);

      // Bullet lists (`* item`, `- item`, indented or not), each list its own block.
      html = html.replace(/^[ \t]*[*-][ \t]+(.+)$/gm, '<li>$1</li>');
      html = html.replace(/(?:<li>.*<\/li>\n?)+/g, (m) => `\n\n<ul>${m.replace(/\n/g, '')}</ul>\n\n`);

      // Bold **…**, italic *…*
      html = html.replace(/\*\*([^*\n]+)\*\*/g, '<strong>$1</strong>');
      html = html.replace(/(^|[^\w*])\*(?=\S)([^*\n]*?\S)\*(?![\w*])/g, '$1<em>$2</em>');

      // Paragraphs
      html = html.split(/\n{2,}/).map(p => {
        p = p.trim();
        if (!p) return '';
        const block = /^<ul/.test(p) || (/^\u0000\d+\u0000$/.test(p) && kept[Number(p.slice(1, -1))].startsWith('<pre'));
        return block ? p : `<p>${p.replace(/\n/g, '<br>')}</p>`;
      }).join('');

      return html.replace(/\u0000(\d+)\u0000/g, (m, i) => kept[Number(i)]);
    }
  }

  window.VersoTooltipView = new VersoTooltipView();
})();
