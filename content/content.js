/**
 * Main content script for Lean Lens.
 * Coordinates hover detection, token resolution, PR diff scanning, and tooltip rendering.
 * Built with hysteresis and debouncing to eliminate flickering.
 */

(function () {
  let settings = {
    enabled: true,
    hoverDelay: 250,
    enablePRScanner: true,
    enableBuiltins: true
  };

  let hoverTimer = null;
  let loadingTimer = null;
  let lastHoveredToken = null;
  let lastHoveredRect = null;
  let rescanDebounceTimer = null;

  /**
   * Load current extension settings.
   */
  function loadSettings() {
    try {
      chrome.runtime.sendMessage({ action: "GET_SETTINGS" }, (res) => {
        if (res && res.settings) {
          settings = Object.assign(settings, res.settings);
        }
      });
    } catch (err) {
      // Keep defaults
    }
  }

  /**
   * Debounced scan of PR diffs to handle virtualized scrolling efficiently.
   */
  function triggerPRScan() {
    if (!settings.enablePRScanner) return;
    if (rescanDebounceTimer) clearTimeout(rescanDebounceTimer);
    rescanDebounceTimer = setTimeout(() => {
      window.LeanPRScanner.scanPage();
      indexProjectFiles();
    }, 350);
  }

  // Declarations read from the PR's files at its commit (and, outside Mathlib, the project
  // files they import): GitHub collapses large diffs, and Loogle only knows Mathlib.
  let projectIndex = null; // promise while a request is running
  const indexedPaths = new Set();
  let indexedPage = null;

  function indexProjectFiles() {
    const m = location.pathname.match(/^\/([^/]+)\/([^/]+)\/pull\/(\d+)/);
    const ctx = window.VersoBinderContext;
    if (!m || !ctx || !window.LeanPRScanner) return;
    const page = `${m[1]}/${m[2]}#${m[3]}`;
    if (indexedPage !== page) { indexedPage = page; indexedPaths.clear(); }
    const paths = window.LeanPRScanner.filePaths().filter(p => !indexedPaths.has(p));
    if (!paths.length) return;
    paths.forEach(p => indexedPaths.add(p));
    const rev = ctx.pageRevision();
    const request = sendMessageP({ action: 'PROJECT_DECLARATIONS', owner: m[1], repo: m[2], pr: m[3], sha: rev.head, paths })
      .then((res) => { if (res && res.declarations) window.LeanPRScanner.addDeclarations(res.declarations); })
      .finally(() => { if (projectIndex === request) projectIndex = null; });
    projectIndex = request;
  }

  /**
   * Initialize PR diff scanning on GitHub.
   */
  function initPRScanner() {
    if (!settings.enablePRScanner) return;
    window.LeanPRScanner.scanPage();
    indexProjectFiles();

    // Re-scan when GitHub mounts new virtualized diff chunks
    const observer = new MutationObserver((mutations) => {
      let shouldRescan = false;
      for (const m of mutations) {
        if (m.addedNodes && m.addedNodes.length > 0) {
          for (const node of m.addedNodes) {
            if (node.nodeType === Node.ELEMENT_NODE) {
              if (node.matches?.('.file, .diff-table, [data-tag="diff-line"], [data-component="diff-file"], [data-component="diff-line"], tr') ||
                  node.querySelector?.('.file, .diff-table, [data-tag="diff-line"], [data-component="diff-line"], tr')) {
                shouldRescan = true;
                break;
              }
            }
          }
        }
        if (shouldRescan) break;
      }

      if (shouldRescan) {
        triggerPRScan();
      }
    });

    observer.observe(document.body, { childList: true, subtree: true });
  }

  /**
   * `Namespace.field` for `receiver.field` when the receiver is a local whose binder
   * type can be read from the surrounding declaration; null otherwise.
   */
  function typedFieldToken(tokenInfo, contextText) {
    const chain = tokenInfo.chainUpToCursor;
    const ctx = window.VersoBinderContext;
    if (!chain || !ctx || !contextText) return null;
    const parts = chain.split('.');
    if (parts.length !== 2 || !/^[a-z_α-ω]/.test(parts[0])) return null;
    const ns = ctx.inferReceiverNamespace(parts[0], contextText);
    return ns ? `${ns}.${parts[1]}` : null;
  }

  /**
   * Generalized field notation whose receiver needs more than a binder lookup:
   * `(f a).field` and `h.f₁.f₂.field`. Returns { token } when the namespace is known
   * here, { chain: { const, path }, field } when the worker must read constant types
   * from Loogle, or null.
   */
  function receiverFor(tokenInfo, contextText) {
    const ctx = window.VersoBinderContext;
    const fields = (tokenInfo.chainUpToCursor || '').split('.').filter(Boolean);
    if (!ctx || fields.length === 0) return null;
    const isLocal = (name) => Boolean(ctx.findBinderType(name, contextText));
    const resolveVar = (v) => {
      const vt = ctx.findBinderType(v, contextText);
      return vt ? ctx.typeHead(vt, null) : null;
    };
    // With the receiver's namespace `ns` known, `ns.f₁` is a constant whose type gives the
    // next namespace; with only a constant known, its type gives the first one.
    const finish = (ns, constName, rest) => {
      if (ns && rest.length === 1) return { token: `${ns}.${rest[0]}` };
      if (ns) {
        constName = `${ns}.${rest[0]}`;
        rest = rest.slice(1);
      }
      if (!constName || rest.length === 0) return null;
      return { chain: { const: constName, path: rest.slice(0, -1) }, field: rest[rest.length - 1] };
    };

    // `(expr).f₁.….field`
    let prefix = tokenInfo.linePrefix;
    if (prefix !== undefined) {
      const lastNl = contextText.lastIndexOf('\n');
      prefix = (lastNl === -1 ? '' : contextText.slice(0, lastNl + 1)) + prefix;
      const inner = ctx.parenReceiver(prefix);
      // `(e : T).field`: the ascribed type decides.
      const ascription = inner && inner.match(/^([^:]*[^:=\s])\s:\s(?!=)([\s\S]+)$/);
      if (ascription) {
        const ns = ctx.typeHead(ascription[2], resolveVar);
        if (ns) return finish(ns, null, fields);
      }
      const head = inner && ctx.applicationHead(inner);
      // `((f x).g y).h`: type the base, then each field in turn.
      const nested = inner && !head ? ctx.termChain(inner) : null;
      if (nested) {
        const segs = nested.base.split('.');
        if (isLocal(segs[0])) {
          const ns = ctx.typeHead(ctx.conclusionOf(ctx.localType(segs[0], contextText)), resolveVar);
          return ns ? finish(ns, null, [...segs.slice(1), ...nested.path, ...fields]) : null;
        }
        const prBase = window.LeanPRScanner && window.LeanPRScanner.find(nested.base);
        if (prBase && prBase.typeSignature) {
          const sig = prBase.typeSignature.replace(/^\S+\s+\S+\s*/, '');
          const ns = ctx.typeHead(ctx.conclusionOf(sig), (v) => {
            const vt = ctx.findBinderType(v, sig);
            return vt ? ctx.typeHead(vt, null) : null;
          });
          if (ns) return finish(ns, null, [...nested.path, ...fields]);
        }
        const rest = [...nested.path, ...fields];
        return { chain: { const: nested.base, path: rest.slice(0, -1), maybeVariable: /^[a-z_]/.test(nested.base), applied: true }, field: rest[rest.length - 1] };
      }
      if (head) {
        const segs = head.split('.');
        if (segs.length === 1 && isLocal(head)) {
          // `(h a b).field`: the conclusion of h's type, after its arguments.
          const ns = ctx.typeHead(ctx.conclusionOf(ctx.findBinderType(head, contextText)), resolveVar);
          return ns ? finish(ns, null, fields) : null;
        }
        // A declaration from this PR (not in Loogle yet): use its signature here.
        const prDecl = window.LeanPRScanner && window.LeanPRScanner.find(head);
        if (prDecl && prDecl.typeSignature) {
          const sig = prDecl.typeSignature.replace(/^\S+\s+\S+\s*/, '');
          const sigVar = (v) => {
            const vt = ctx.findBinderType(v, sig);
            return vt ? ctx.typeHead(vt, null) : null;
          };
          const conclusion = ctx.conclusionOf(sig);
          const ns = ctx.typeHead(conclusion, sigVar);
          if (ns) {
            const result = finish(ns, null, fields);
            // `(e r).field` where `e : A →* B`: the application coerces `e` to a function, so
            // the field may live in the codomain's namespace instead.
            const applied = ctx.splitApp(inner).slice(1).filter(a => !/^\(\s*[\w']+\s*:=/.test(a)).length > 0;
            const codomainNs = applied ? ctx.typeHead(ctx.codomainOf(conclusion), sigVar) : null;
            if (result && codomainNs && codomainNs !== ns) result.alt = finish(codomainNs, null, fields);
            return result;
          }
        }
        if (segs.length === 1 && /^[a-z_α-ω]/.test(head) && !ctx.findUntypedBinder(head, contextText) &&
            !ctx.findBinderType(head, contextText)) {
          // Maybe a file-level `variable` applied to arguments, or an unqualified constant.
          return { chain: { const: head, path: fields.slice(0, -1), maybeVariable: true, applied: true }, field: fields[fields.length - 1] };
        }
        if (segs.length === 2 && isLocal(segs[0])) {
          // `(hf.comp hg).field`: hf's namespace gives the constant `NS.comp`.
          const ns = ctx.inferReceiverNamespace(segs[0], contextText);
          return ns ? finish(null, `${ns}.${segs[1]}`, fields) : null;
        }
        return finish(null, head, fields);
      }
    }

    // `h.f₁.….field` with three or more segments: type each step in turn.
    if (fields.length >= 3 && isLocal(fields[0])) {
      const ns = ctx.inferReceiverNamespace(fields[0], contextText);
      return ns ? finish(ns, null, fields.slice(1)) : null;
    }
    // `x.f₁.….field` where `x` isn't bound here: a file-level `variable` (`hT.out`) or a
    // lowercase constant (`one_div_pos.mpr`). The worker tries both.
    // Two-segment `E.foo` with a bound `E` (uppercase locals are common: `E K L : Type*`).
    if (fields.length === 2 && isLocal(fields[0]) && !/^[a-z_α-ω]/.test(fields[0])) {
      const ns = ctx.inferReceiverNamespace(fields[0], contextText);
      return ns ? { token: `${ns}.${fields[1]}` } : null;
    }
    // A constant declared in the PR or project (`enormAt_X.trans_lt`): its statement's head.
    // Not for namespaces (`CNF.zero_right` is itself declared) or aliases (no written type).
    const scanner = window.LeanPRScanner;
    if (fields.length >= 2 && !isLocal(fields[0]) && /^[a-z_]/.test(fields[0]) && scanner && !scanner.declarations.has(fields.join('.'))) {
      const prHead = scanner.declarations.get(fields[0]);
      if (prHead && prHead.typeSignature && prHead.kind !== 'alias') {
        const sig = prHead.typeSignature.replace(/^\S+\s+\S+\s*/, '');
        const ns = ctx.typeHead(ctx.conclusionOf(sig), (v) => {
          const vt = ctx.findBinderType(v, sig);
          return vt ? ctx.typeHead(vt, null) : null;
        });
        if (ns) return finish(ns, null, fields.slice(1));
      }
    }
    // Short capitalised names (`E.algebraMap_apply`) may be `variable`s, like lowercase ones.
    if (fields.length >= 2 && (/^[a-z_α-ω]/.test(fields[0]) || /^[A-Z][\w']?$/.test(fields[0])) && !isLocal(fields[0])) {
      return {
        chain: { const: fields[0], path: fields.slice(1, -1), maybeVariable: true },
        field: fields[fields.length - 1]
      };
    }
    return null;
  }

  // Notation that names a constant.
  const NOTATION_ALIASES = {
    'ℝ': 'Real', 'ℂ': 'Complex', 'ℕ': 'Nat', 'ℤ': 'Int', 'ℚ': 'Rat', 'π': 'Real.pi', "''": 'Set.image'
  };

  /**
   * Surrounding declaration text, the typed token for dot notation, and (for bare
   * identifiers that aren't locals) where the line lives so the worker can read the
   * file's `namespace`/`open`s.
   */
  function lookupContext(tokenInfo) {
    const ctx = window.VersoBinderContext;
    const out = { queryToken: tokenInfo.token, fileRef: null, contextText: '', local: null, receiver: null, namedArg: null, structField: null, skip: false, alt: null };
    if (!ctx) return out;
    try {
      out.contextText = ctx.contextFromDom(tokenInfo.textNode) || '';
      // A bare name (not `x.field`) bound in this declaration is a local variable.
      const chain = tokenInfo.chainUpToCursor || tokenInfo.token;
      // Bundled-map notation (`→ₛₗ[σ]`, `≃+*`): show the structure it stands for.
      if (tokenInfo.arrowNotation) {
        out.queryToken = ctx.typeHead(`A ${chain} B`, null) || chain;
        return out;
      }
      if (!chain.includes('.')) {
        out.local = ctx.localVariableInfo(chain, out.contextText);
        if (out.local) return out;
      }
      // `h.1`, `h.2.1`: anonymous projections of a local.
      out.local = ctx.projectionInfo(chain, out.contextText);
      if (out.local) return out;
      const linePrefix = tokenInfo.linePrefix || '';
      const lineSuffix = tokenInfo.lineSuffix || '';
      // Names on an `open … in` / `open scoped …` line are namespaces (possibly notation-only).
      if (/^\s*open\b/.test(linePrefix)) {
        const ns = tokenInfo.fullChain || chain;
        out.local = {
          name: chain, kind: 'namespace', source: 'local_var',
          typeSignature: `namespace ${chain}`,
          docstring: `Namespace opened here${/\bscoped\b/.test(linePrefix) ? ' for its scoped notation and instances' : ''}` +
            (ns !== chain ? ` (part of \`${ns}\`)` : '') + '.'
        };
        return out;
      }
      // `section Foo` / `end Foo` labels and universe names (`Type u`, `Sort (max u v)`).
      if (/^\s*(?:(?:noncomputable|public|private)\s+)*(?:section|end)\s+$/.test(linePrefix) ||
          /\b(?:Type|Sort)\s*\(?(?:max\s+|imax\s+)?(?:[\w\u0370-\u03FF]+\s+)*$/.test(linePrefix) ||
          /^\s*universe\b/.test(linePrefix)) {
        out.skip = true;
        return out;
      }
      // `| ne_zero o ho IH =>`: the case of a `match` / `induction … with`.
      if (!chain.includes('.') && /^\s*\|\s*$/.test(linePrefix) && /=>/.test(lineSuffix)) {
        out.local = {
          name: chain, kind: 'variable', source: 'local_var',
          typeSignature: `| ${chain} …`,
          docstring: `Case \`${chain}\` of a \`match\` / \`induction … with\` / \`cases … with\` alternative; the names after it are bound in that case.`
        };
        return out;
      }
      // `field := …` / `toFun x := …` in a `where` / `{ }` block: a field of the structure being built.
      if (!chain.includes('.') && /^(?:(?:\s+[\w'\u0370-\u03FF\u2080-\u2089]+)|(?:\s*\([^)]*\)))*\s*:=/.test(lineSuffix) &&
          /(^\s*|[{,]\s*|\bwith\s+)$/.test(linePrefix)) {
        const ns = ctx.structureBeingBuilt(out.contextText);
        if (ns) {
          out.queryToken = `${ns}.${chain}`;
          out.structField = { ns, field: chain };
          out.fileRef = ctx.fileRefFromDom(tokenInfo.textNode);
          return out;
        }
      }
      // `foo (b := a)`: `b` is foo's parameter.
      if (!chain.includes('.') && /^\s*:=/.test(tokenInfo.lineSuffix || '')) {
        const lastNl = out.contextText.lastIndexOf('\n');
        const prefix = (lastNl === -1 ? '' : out.contextText.slice(0, lastNl + 1)) + (tokenInfo.linePrefix || '');
        const fn = ctx.namedArgFunction(prefix);
        if (fn) {
          const decl = window.LeanPRScanner && window.LeanPRScanner.find(fn);
          out.local = decl ? ctx.namedArgInfo(chain, fn, decl.typeSignature) : null;
          if (out.local) return out;
          out.namedArg = { fn, arg: chain };
        }
      }
      if (!chain.includes('.') && NOTATION_ALIASES[chain]) {
        out.queryToken = NOTATION_ALIASES[chain];
        out.fileRef = ctx.fileRefFromDom(tokenInfo.textNode);
        return out;
      }
      const receiver = receiverFor(tokenInfo, out.contextText);
      if (receiver && receiver.alt) out.alt = receiver.alt;
      if (receiver && receiver.token) {
        out.queryToken = receiver.token;
      } else if (receiver && receiver.chain) {
        out.receiver = receiver.chain;
        out.queryToken = receiver.field;
      } else {
        out.queryToken = typedFieldToken(tokenInfo, out.contextText) || tokenInfo.token;
      }
      // The file reference also lets the worker find `variable`s and resolve receivers' constants.
      out.fileRef = ctx.fileRefFromDom(tokenInfo.textNode);
    } catch (err) {
      // Fall back to the plain token.
    }
    return out;
  }

  /** `chrome.runtime.sendMessage` as a promise (resolves to null on failure). */
  function sendMessageP(message) {
    return new Promise((resolve) => {
      try {
        chrome.runtime.sendMessage(message, (res) => resolve(chrome.runtime.lastError ? null : res));
      } catch (err) {
        resolve(null);
      }
    });
  }

  /**
   * Signature (`binders : conclusion`) of a constant used as a rewrite rule: a declaration
   * from this PR if it has exactly that name, else Loogle (via the worker), else a PR
   * declaration matched by its short name.
   */
  async function constantSignature(name, fileRef) {
    const pr = window.LeanPRScanner;
    const strip = (d) => d.typeSignature.replace(/^\S+\s+\S+\s*/, '');
    const exact = pr && pr.declarations.get(name);
    if (exact && (exact.name === name || exact.name === `_root_.${name}`)) return strip(exact);
    const res = await sendMessageP({ action: 'CONSTANT_SIGNATURE', name, fileRef });
    if (res && res.type) return res.type;
    const loose = pr && pr.find(name);
    return loose && loose.typeSignature ? strip(loose) : null;
  }

  /**
   * Finish a local-variable tooltip that needs more work: a type inferred by the worker
   * (`obtain h | h := le_or_gt b 1`), a structure field (`e.1`), and replaying the tactics
   * that changed the hypothesis since it was bound (`rw [Set.uIcc_of_le h] at hy`).
   */
  async function refineLocal(shown, contextText, fileRef) {
    const ctx = window.VersoBinderContext;
    let info = Object.assign({}, shown);
    if (info.inferNeeded && ctx) {
      // Instantiate the term's head (a PR declaration or a Loogle constant) with its arguments.
      const res = await ctx.inferPending(info.inferNeeded, contextText, (name) => constantSignature(name, fileRef));
      if (res && res.typeSignature) {
        info.typeSignature = res.typeSignature;
        info.docstring = `Local variable from \`${info.inferNeeded.term.length > 80 ? info.inferNeeded.term.slice(0, 77) + '…' : info.inferNeeded.term}\`; ` +
          `type inferred from the statement of \`${res.from}\`` + (res.note ? ` (${res.note})` : '') +
          (res.unresolved && res.unresolved.length ? `; \`${res.unresolved.join('`, `')}\` couldn't be determined from the arguments` : '') + '.';
        if (info.replay) {
          info.replay = Object.assign({}, info.replay, { baseType: res.typeSignature.slice(info.name.length + 3), lead: info.docstring });
        }
      }
    }
    if (info.structureNeeded) {
      const res = await sendMessageP(Object.assign({ action: 'STRUCTURE_FIELD' }, info.structureNeeded));
      if (res && res.field) {
        info.typeSignature = `${info.name} : ${res.field.type}`;
        info.docstring = `Field \`${res.field.name}\` of \`${res.structure}\`.\n\n` + info.docstring;
      }
    }
    if (info.replay && info.replay.baseType && ctx) {
      const result = await ctx.replayChanges(info.replay.baseType, info.replay.changes, contextText,
        (name) => constantSignature(name, fileRef));
      info = Object.assign(info, ctx.describeReplay(info, result));
    }
    return info;
  }

  /**
   * Is the hovered word comment / docstring prose? GitHub wraps comments in `.pl-c`.
   * Code in backticks inside a docstring still counts as code.
   */
  function isInProse(tokenInfo) {
    const node = tokenInfo.textNode;
    const el = node && (node.nodeType === 1 ? node : node.parentElement);
    const inComment = Boolean(el && el.closest && el.closest('.pl-c')) ||
      /(^|[^-])--(?!-)/.test((tokenInfo.linePrefix || '').replace(/`[^`]*`/g, ''));
    if (!inComment) return false;
    const ticks = ((tokenInfo.linePrefix || '').match(/`/g) || []).length;
    return ticks % 2 === 0;
  }

  /** Inside an attribute list `@[simp, deprecated (since := …)]`? */
  function isInAttribute(tokenInfo) {
    const prefix = tokenInfo.linePrefix || '';
    const open = prefix.lastIndexOf('@[');
    return open !== -1 && prefix.indexOf(']', open) === -1;
  }

  /**
   * Resolve and display hover definition.
   */
  function triggerHoverLookup(tokenInfo) {
    const { token, subToken, boundingRect } = tokenInfo;
    const lookup = lookupContext(tokenInfo);
    if (lookup.skip) return;

    // 0. Local variables shadow everything else: show their type.
    if (lookup.local) {
      window.VersoTooltipView.show(lookup.local, boundingRect);
      const needsMore = lookup.local.inferNeeded || lookup.local.structureNeeded || lookup.local.replay;
      if (needsMore) {
        const fileRef = window.VersoBinderContext && window.VersoBinderContext.fileRefFromDom(tokenInfo.textNode);
        refineLocal(lookup.local, lookup.contextText, fileRef).then((info) => {
          if (lastHoveredToken === token && info) window.VersoTooltipView.show(info, boundingRect);
        }).catch(() => { /* keep the provisional tooltip */ });
      }
      return;
    }

    // 1. Check if defined in current PR diff
    if (settings.enablePRScanner && window.LeanPRScanner) {
      // The typed name first (`SortedGT.sort_toFinset`), then the hovered word itself.
      const pr = window.LeanPRScanner;
      const prDecl = pr.find(lookup.queryToken) ||
        (lookup.queryToken === token || !lookup.queryToken.includes('.') ? pr.find(token) || (subToken ? pr.find(subToken) : null) : null);
      if (prDecl) {
        window.VersoTooltipView.show(prDecl, boundingRect);
        return;
      }
      // The PR's files are still being read: try again once they are.
      if (projectIndex) {
        projectIndex.then(() => { if (lastHoveredToken === token) triggerHoverLookup(tokenInfo); });
        return;
      }
    }

    // 2. Check Built-ins (tactics, core types)
    if (settings.enableBuiltins && window.VersoBuiltins) {
      const builtin = window.VersoBuiltins.get(token) || (subToken ? window.VersoBuiltins.get(subToken) : null);
      if (builtin) {
        window.VersoTooltipView.show(builtin, boundingRect);
        return;
      }
    }

    // Single-letter identifiers are local variables, not global Mathlib definitions.
    // Without a file reference (to look for `variable` declarations) there is nothing to show.
    if (lookup.queryToken.length <= 1 && !lookup.fileRef) {
      return;
    }

    // Dot notation on a local (`hl.nodup` with `hl : l.SortedLT`): resolve the field
    // in the namespace of the receiver's type, as Lean does (`List.SortedLT.nodup`).
    const { queryToken, fileRef, contextText, receiver, namedArg, structField } = lookup;

    // 3. Query background worker (Loogle / local companion server)
    // To prevent flicker, do NOT show loading immediately.
    // If the lookup takes longer than 180ms, only then show a subtle loading spinner.
    if (loadingTimer) clearTimeout(loadingTimer);
    loadingTimer = setTimeout(() => {
      if (lastHoveredToken === token) {
        window.VersoTooltipView.showLoading(token, boundingRect);
      }
    }, 180);

    try {
      chrome.runtime.sendMessage(
        {
          action: "LOOKUP_TOKEN", token: queryToken, subToken: subToken,
          fileRef: fileRef, contextText: contextText.slice(-4000),
          fullChain: tokenInfo.fullChain, alt: lookup.alt,
          tacticPosition: Boolean(tokenInfo.tacticPosition) && !receiver,
          receiver: receiver, namedArg: namedArg, structField: structField
        },
        (res) => {
          if (loadingTimer) {
            clearTimeout(loadingTimer);
            loadingTimer = null;
          }

          // Verify cursor hasn't moved away to another token while fetching
          if (lastHoveredToken !== token) return;

          if (res && res.success && res.data) {
            window.VersoTooltipView.show(res.data, boundingRect);
          } else {
            // Not found; quietly hide tooltip without flashing
            window.VersoTooltipView.hide(false);
          }
        }
      );
    } catch (err) {
      if (loadingTimer) clearTimeout(loadingTimer);
      window.VersoTooltipView.hide(false);
    }
  }

  /**
   * Handle mouse movements on GitHub code and diffs.
   * Uses hysteresis to prevent micro-jitter blinking.
   */
  function handleMouseMove(e) {
    if (!settings.enabled) return;

    // Ignore if tooltip is pinned
    if (window.VersoTooltipView.isPinned) return;

    // 1. Check if mouse is hovering over the tooltip itself
    const root = document.getElementById('verso-hover-root');
    if (root && root.contains(e.target)) {
      window.VersoTooltipView.clearHideTimer();
      return;
    }

    // 2. Hysteresis: if tooltip is visible, check if mouse is still inside the active token's area
    if (window.VersoTooltipView.isVisible() && lastHoveredRect) {
      const padX = 14;
      const padY = 8;
      const inX = e.clientX >= (lastHoveredRect.left - padX) && e.clientX <= (lastHoveredRect.right + padX);
      const inY = e.clientY >= (lastHoveredRect.top - padY) && e.clientY <= (lastHoveredRect.bottom + padY);

      if (inX && inY) {
        // Mouse is still within the boundary of the active token; keep it stable!
        window.VersoTooltipView.clearHideTimer();
        return;
      }
    }

    // 3. Check if target is inside a Lean code block or diff
    if (!window.LeanTokenizer.isInsideLeanContext(e.target)) {
      if (hoverTimer) {
        clearTimeout(hoverTimer);
        hoverTimer = null;
      }
      if (loadingTimer) {
        clearTimeout(loadingTimer);
        loadingTimer = null;
      }
      lastHoveredToken = null;
      lastHoveredRect = null;
      window.VersoTooltipView.scheduleHide(180);
      return;
    }

    // 4. Extract Lean token at cursor
    let tokenInfo = window.LeanTokenizer.resolveTokenFromEvent(e);
    if (tokenInfo && (isInProse(tokenInfo) || isInAttribute(tokenInfo))) tokenInfo = null;
    if (!tokenInfo || !tokenInfo.token || tokenInfo.isKeyword) {
      if (hoverTimer) {
        clearTimeout(hoverTimer);
        hoverTimer = null;
      }
      if (loadingTimer) {
        clearTimeout(loadingTimer);
        loadingTimer = null;
      }
      lastHoveredToken = null;
      lastHoveredRect = null;
      window.VersoTooltipView.scheduleHide(180);
      return;
    }

    // If still hovering the exact same token, keep tooltip active
    if (lastHoveredToken === tokenInfo.token) {
      window.VersoTooltipView.clearHideTimer();
      return;
    }

    // New token hovered: clear pending timers
    if (hoverTimer) {
      clearTimeout(hoverTimer);
      hoverTimer = null;
    }
    if (loadingTimer) {
      clearTimeout(loadingTimer);
      loadingTimer = null;
    }

    lastHoveredToken = tokenInfo.token;
    lastHoveredRect = tokenInfo.boundingRect;

    // Debounce hover before showing definition
    hoverTimer = setTimeout(() => {
      triggerHoverLookup(tokenInfo);
    }, settings.hoverDelay || 250);
  }

  /**
   * Bind event listeners.
   */
  function initListeners() {
    document.addEventListener('mousemove', handleMouseMove, { passive: true });

    // Handle GitHub SPA soft navigations (Turbo / PJAX)
    const handleNavigation = () => {
      window.VersoTooltipView.hide(true);
      setTimeout(() => {
        initPRScanner();
      }, 500);
    };

    document.addEventListener('turbo:render', handleNavigation);
    document.addEventListener('turbo:load', handleNavigation);
    document.addEventListener('pjax:end', handleNavigation);
    window.addEventListener('popstate', handleNavigation);
  }

  /**
   * Handle messages from Popup or Background
   */
  chrome.runtime.onMessage.addListener((request, sender, sendResponse) => {
    if (request.action === "GET_PAGE_INFO") {
      const isLean = window.LeanTokenizer.isInsideLeanContext(document.body) ||
                     Boolean(document.querySelector('.file-header[data-path$=".lean"], a[title$=".lean"]'));
      sendResponse({
        isLeanDetected: isLean,
        prDefinitionsCount: window.LeanPRScanner.declarations.size,
        declarations: Array.from(window.LeanPRScanner.declarations.values()).slice(0, 20)
      });
      return true;
    }

    if (request.action === "SETTINGS_UPDATED") {
      loadSettings();
      sendResponse({ success: true });
      return true;
    }
  });

  // Exposed for the test suite.
  window.VersoContentInternals = { receiverFor, lookupContext, isInProse, isInAttribute, refineLocal };

  // Startup
  loadSettings();
  initListeners();
  setTimeout(initPRScanner, 500);
})();
