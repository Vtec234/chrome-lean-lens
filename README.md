# Lean Lens: Lean 4 Hover Inspector for GitHub

A Chrome extension for reviewing **Lean 4** pull requests on GitHub. Hover over an identifier, tactic or local variable in a diff and Lean Lens shows its type signature, docstring and where it comes from, without leaving the page.

It works on both GitHub diff views (the classic `/files` view and the newer `/changes` view) and on file pages.

---

## What a hover shows

- **Mathlib / Lean declarations**: signature, docstring, module and a link to the Mathlib docs, via [Loogle](https://loogle.lean-lang.org/).
- **Declarations added in the PR**: indexed from the diff (`theorem`, `lemma`, `def`, `structure`, `alias`, …) with multi-line signatures and docstrings, plus a "Jump to line in PR" button.
- **Tactics**: docstrings for ~470 tactics, parsed from Mathlib's tactic reference and cached for a week (`fun_prop`, `positivity`, `filter_upwards`, …).
- **Local variables and hypotheses**: their type, whether written (`(hb : 0 < b)`, `have h : …`, `by_cases h : …`, file-level `variable`s) or inferred:
  - `intro` / `rintro` / `fun`: binders peeled off the goal (`∀ x ∈ s, …`, `A → B`, `s ⊆ t`);
  - `obtain` / `rcases`: patterns destructured through `∃` / `∧` / `↔` / `∨` (for constant terms such as `le_or_gt b 1`, the lemma's signature is instantiated with the arguments); the `·` bullet you hover in picks the case;
  - anonymous projections such as `hy.1`, `hy.2`;
  - a warning when the hypothesis was changed earlier (`rw … at h`, `simp at h`).
- **Named arguments**: `(b := a)` shows the parameter `b` of the function being applied.

## How names are resolved

Lean Lens works from the text of the diff, the file at the PR's commit (fetched from `raw.githubusercontent.com`) and Loogle; it does not run Lean.

- **Dot notation** (`hl.nodup`, `(ContinuousAt.tendsto h).mono_left`, `hT.out.le`): the receiver's type is read from its binder, a file-level `variable`, a PR declaration, or a Loogle signature (conclusion plus argument substitution), step by step for longer chains. Bundled-map notations (`→ₗ[R]`, `≃+*`, `→ₘₛₗ[σ]`, ~60 in total) map to their structures.
- **Bare names** (`cons`, `pairwise_sort`): the `namespace` / `section` / `open` scope at the hovered line decides which candidates exist; root names and exported class fields (`mul_zero`, `star`) win over opened namespaces, then the current namespace.
- When several candidates remain, the tooltip lists them instead of guessing.
- Comments, docstring prose (except code in backticks), attributes, universe names and section labels are ignored.

---

## Installation

1. Open `chrome://extensions` and switch on **Developer mode** (top right).
2. Click **Load unpacked** and select the cloned `chrome-lean-lens` folder.
3. Open a Lean PR on GitHub (for example in [mathlib4](https://github.com/leanprover-community/mathlib4/pulls)), go to **Files changed**, and hover.

After pulling updates, click **Reload** on the extension card and refresh the GitHub tab.

## Testing

```bash
node test/run_tests.js
```

`test/demo_pr.html` is a static page that imitates a GitHub PR diff for trying tooltips offline.

---

## Project layout

```
chrome-lean-lens/
├── manifest.json                  # Manifest V3 configuration
├── icons/                         # Icons (generate_icons.py redraws them)
├── background/
│   └── service_worker.js          # Loogle, file scope, tactic docs, caching, companion server
├── content/
│   ├── lean_tokenizer.js          # Token under the cursor, tactic position, notation
│   ├── binder_context.js          # Binders, type heads, receivers, local type inference
│   ├── pr_scanner.js              # Declarations added in the PR
│   ├── builtins_db.js             # Offline docs for core tactics and types
│   ├── tooltip_view.js            # Tooltip UI and Markdown rendering
│   ├── content.js                 # Hover handling and lookup orchestration
│   └── content.css                # Tooltip styles (light / dark)
├── popup/                         # Toolbar popup with symbol search
├── options/                       # Settings page
├── server/                        # Optional local companion server
└── test/                          # Unit tests and the demo page
```

## Options

Right-click the toolbar icon → **Options**:
- **Hover delay** (default 250 ms)
- **PR declaration scanner**, **Loogle lookups**, **built-in tactic docs**: on/off
- **Theme**: match GitHub, Slate Dark, or Clean Light
- **Local companion server**: host/port for private projects

## Local companion server (optional)

For private Lean repositories that Loogle doesn't index:

```bash
python3 server/companion_server.py --port 8000 --project /path/to/my-lean-project
```

Then enable **Local companion server** in the options and click **Test Connection**. The server searches the project's `.lean` files for declarations by name; it does not run Lean.
