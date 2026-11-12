# Verso: Lean 4 GitHub Code Inspector (Chrome Extension)

A Chrome extension designed specifically for **Lean 4** code intelligence on GitHub, tailored for **pull request reviews** and repository browsing. Hovering your cursor over any Lean identifier, tactic, or definition instantly displays its definition, type signature, and docstrings rendered in **Verso**'s documentation style.

---

## Key Features

1. **GitHub PR Review Intelligence (In-PR Declaration Scanner)**:
   - When reviewing a PR, new lemmas or definitions introduced in the PR diff aren't published to upstream documentation yet.
   - Verso automatically scans the PR diff (unified and split diffs) to index newly added/modified `def`, `theorem`, `lemma`, `inductive`, `structure`, `class`, and `instance` declarations along with their `/-- ... -/` docstrings.
   - Displays a prominent **"✨ Defined in this PR"** badge and provides a **"Jump to line in PR &rarr;"** button that scrolls directly to where the lemma was introduced.

2. **Loogle & Mathlib 4 Deep Integration**:
   - Queries the official [Loogle](https://loogle.lean-lang.org/) semantic engine for Lean 4 and Mathlib definitions.
   - Direct deep-links to the exact symbol in the official Mathlib 4 API documentation.

3. **Built-in Zero-Latency Knowledge Base**:
   - Includes an offline dictionary of core Lean 4 tactics (`simp`, `rw`, `apply`, `exact`, `intro`, `cases`, `rcases`, `induction`, `obtain`, `ext`, `ring`, `linarith`, `omega`, `norm_num`, `aesop`, `tauto`, etc.) and prelude types (`Nat`, `Int`, `Real`, `List`, `Finset.sum`, `Continuous`, etc.).
   - Instant response with zero network latency.

4. **Verso-Inspired Tooltip Presentation**:
   - Styled after Verso's interactive documentation (`.hover-info`):
     - Syntax-highlighted code blocks for signatures (`∀`, `∃`, `→`, implicit binders `{α : Type}`, typeclasses `[Group G]`).
     - Rendered markdown docstrings (with formatting, bullet lists, inline code, and math expressions).
     - Color-coded badges for declaration kinds (`def`, `theorem`, `lemma`, `structure`, `tactic`).
   - Adapts to GitHub's **dark and light themes** automatically.

5. **Reviewer Productivity Controls**:
   - **Pin Mode (<kbd>Alt</kbd> or 📌 icon)**: Pins the tooltip so you can select, copy, scroll, or keep it open while comparing code side-by-side.
   - **Quick Copy**: One-click button to copy the identifier name or type signature.
   - **Popup Symbol Search**: Search any Lean 4 symbol or tactic right from the extension popup icon in your browser toolbar without switching tabs.
   - **Optional Local Companion Server**: For private Lean projects or offline environments, run `server/companion_server.py` to query local Lake builds.

---

## Installation Guide

### Loading into Google Chrome (or Chromium / Brave / Edge)

1. Open Chrome and navigate to:
   ```
   chrome://extensions
   ```
2. In the top-right corner, toggle **Developer mode** to **ON**.
3. Click the **Load unpacked** button in the top-left.
4. Select the project directory:
   ```
   /Users/seewoolee/Documents/development/chrome-verso
   ```
5. The extension **"Verso: Lean 4 GitHub Code Inspector"** will appear in your extensions list.

---

## How to Test

### 1. Test using the Included PR Review Demo Page
We include a realistic GitHub PR diff simulator in `test/demo_pr.html`:

1. In Chrome, press <kbd>Cmd</kbd> + <kbd>O</kbd> (or <kbd>Ctrl</kbd> + <kbd>O</kbd>) and open:
   ```
   /Users/seewoolee/Documents/development/chrome-verso/test/demo_pr.html
   ```
2. Hover over:
   - `continuous_extend_dense` &rarr; Notice the **✨ Defined in this PR** badge and docstring. Click **"Jump to line 123 in PR"**!
   - `simp`, `rw`, `obtain`, `intro` &rarr; Notice the tactic docstrings and usage guides.
   - `Continuous`, `TopologicalSpace`, `Finset.sum` &rarr; Notice the type signatures and documentation links.
   - Press <kbd>Alt</kbd> while hovering to pin the tooltip.

### 2. Test on Real GitHub Pull Requests
Open any Lean 4 repository or PR on GitHub (for example, on [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4/pulls) or [leanprover/lean4](https://github.com/leanprover/lean4/pulls)):
1. Navigate to the **"Files changed"** tab of any Lean PR.
2. Hover over Lean keywords, types, or declarations.
3. The Verso inspector tooltip will appear with the corresponding definition and docstring!

---

## Extension Structure

```
chrome-verso/
├── manifest.json                  # Manifest V3 configuration
├── icons/                         # 16, 32, 48, 128px icons & vector SVG
├── background/
│   └── service_worker.js         # API coordinator (Loogle, caching, local server)
├── content/
│   ├── builtins_db.js            # Offline Lean 4 core tactics & types dictionary
│   ├── lean_tokenizer.js         # Identifies dotted tokens & handles Lean syntax
│   ├── pr_scanner.js             # Parses PR diffs for local definitions & docstrings
│   ├── tooltip_view.js           # Verso-styled hover UI & markdown renderer
│   ├── content.js                # Coordinates events on GitHub pages & diffs
│   └── content.css               # Tooltip styling with light/dark theme support
├── popup/
│   ├── popup.html                # Popup UI with instant symbol search & status
│   ├── popup.css
│   └── popup.js
├── options/
│   ├── options.html              # Settings for hover delay, sources, and themes
│   ├── options.css
│   └── options.js
├── server/
│   ├── companion_server.py       # Optional local Lean Lake companion server
│   └── README.md
├── test/
│   ├── demo_pr.html              # Interactive GitHub PR review test bed
│   └── run_tests.js              # Automated unit tests
└── README.md
```

---

## Configuration & Options

Click the Verso icon in the Chrome toolbar and click the gear icon (or right-click &rarr; **Options**) to configure:
- **Hover Trigger Delay**: Slider from 100ms to 1000ms (default 250ms).
- **In-PR Local Declaration Scanner**: Toggle on/off PR-local definitions indexing.
- **Loogle Lean 4 / Mathlib API**: Toggle on/off online semantic lookups.
- **Built-in Knowledge Base**: Toggle on/off tactic explanations.
- **Visual Theme**: Match GitHub (automatic), Verso Dark, or Verso Light.
- **Local Verso Server**: Configure local host/port (e.g., `http://127.0.0.1:8000`) for private Lean projects.

---

## Local Companion Server (Optional)

If you are reviewing PRs for private Lean repositories not indexed on Loogle:
```bash
python3 server/companion_server.py --port 8000 --project /path/to/my-lean-project
```
Enable **"Local Verso Companion Server"** in the extension options page and click **"Test Connection"**.
