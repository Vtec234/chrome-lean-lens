# Lean Lens: Lean 4 Hover Inspector for GitHub

A Chrome extension for reviewing **Lean 4** pull requests on GitHub. Hover over an identifier, tactic or local variable in a diff and Lean Lens shows its type signature, docstring and where it comes from, without leaving the page.

It works on both GitHub diff views (the classic `/files` view and the newer `/changes` view) and on file pages.

---

## What a hover shows

- **Terms**: hover the space between a function and its arguments, a bracket or an operator, and you get the term there with its type, as in Lean's infoview: `a b : Y`, `abs_le.mp h : -1 ≤ x ∧ x ≤ 1`, `2 : ℕ` for the exponent in `x ^ 2`. The type is worked out from local types and the signatures of the constants involved: arguments' types, anonymous constructors `⟨h₁, h₂⟩`, the declared type in `have h : T := …`, and how the term is used all fix implicit arguments. Arguments still unknown show as `?b`, as Lean shows unassigned metavariables. Bundled maps work the same way, including semilinear ones (`→ₛₗ[σ]`, `≃ₛₗ[σ]`; `→ₗ[R]` is `→ₛₗ[RingHom.id R]`): `map f : (⨂[R] (i : ι), s i) →ₛₗ[σ₁₂] ⨂[R₂] (i : ι), t i`, and a map applied to a point prints `(f i) (x i)`, as Lean prints the coercion. Types of types get Lean's universe names: `CommSemiring R : Type u_4`, `(i : ι) → AddCommMonoid (s i) : Type (max u_1 u_8)`. Binders print as Lean prints them, with their types worked out from their use: `Π i, s i` is `(i : ι) → s i`, `⨂[R] i, s i` is `⨂[R] (i : ι), s i`. Terms broken across lines are read whole. When the type can't be worked out, no tooltip appears. As in Lean, an operator, parentheses, field notation, `∑` and other notations show their docstring under the type (`a + b` computes the sum of `a` and `b`…), read from Loogle and cached for a week.
- **Hover shading**: the code a tooltip describes is shaded while it is open, like the editor's hover highlight: a whole term, on every line it spans, or a name.
- **Mathlib / Lean declarations**: the signature as Lean's hover prints it (`mul_pos.{u_1} {α : Type u_1} [MulZeroClass α] … : 0 < a * b`), docstring, module and a link to the Mathlib docs, via [Loogle](https://loogle.lean-lang.org/).
- **Declarations added in the PR**: indexed from the diff (`theorem`, `lemma`, `def`, `structure`, `alias`, …) with multi-line signatures and docstrings, plus a "Jump to line in PR" button. Signatures include the section `variable`s a declaration takes, the way Lean decides it. A definition takes the variables it mentions anywhere; a theorem only those in its statement. Both also take the variables these depend on, and a theorem every instance argument whose variables are all included. `variable {K} in`, `omit … in` and `include … in` are applied too. So `def gelfandRadiusNorm (x : L)` shows as `gelfandRadiusNorm.{u_1, u_2} (K : Type u_1) (L : Type u_2) [NormedField K] [Field L] [Algebra K L] (x : L) : ℝ`. A variable declared again shadows the earlier one, whose instance arguments then don't come along (its universe is still counted, as Lean counts it). Names a body binds (`fun t ↦ …`, `invFun t := …`) aren't the variable `t`. Instance arguments Lean finds by instance search come along with what they fix: `≃ₛₗ[σ₁₂]` takes `{σ₂₁}` and its `RingHomInvPair`s, `g ∘ₛₗ f` takes `{σ₁₃}` and `[RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]`. A definition or structure takes only the instances it uses, as Lean drops the rest. The source alone can't always tell, so instances that often go unused (`[Fintype ι]`, `[DecidableEq ι]`, `[Nonempty ι]`, …) are taken only on a sign of use: `∑ i, …`, `univ`, `card`, `if`, or a call to a declaration of the file that takes one. Others are assumed used. A structure's fields are declarations too, as the projections Lean makes: `Link.c {ι : Type} {R : Rectangle} {T : ι → Rectangle} (self : Link R T) : ℝ`. Signatures print as Lean's hover prints them. Leading `∀` binders are parameters (`invol_mem … (t : ℕ × ℕ × ℕ) : t ∈ S p → …`), and consecutive binders of one kind and type are one group (`(a b : ℕ)`). `∃` binders have no types (`∃ n, …`), and `@[pp_nodot]` constants have no dot notation (`Nat.Prime p`, `Real.exp x`). A structure without a written type is a `Type`.
- **Tactics**: docstrings for ~470 tactics, parsed from Mathlib's tactic reference and cached for a week (`fun_prop`, `positivity`, `filter_upwards`, …).
- **Local variables and hypotheses**: their type, whether written (`(hb : 0 < b)`, `have h : …`, `by_cases h : …`, file-level `variable`s, with Lean's universe names: `s : ι → Type u_8`) or inferred:
  - untyped binders (`∀ i, AddCommMonoid (s i)`, `fun i ↦ f i (x i)`, `⨂[R] i, s i`): from what they're applied to (`s : ι → Type*` gives `i : ι`; `e.symm i` with `e : ι ≃ ι₂` gives `i : ι₂`);
  - `intro` / `rintro` / `fun`: binders peeled off the goal (`∀ x ∈ s, …`, `A → B`, `s ⊆ t`);
  - `obtain` / `rcases`: patterns destructured through `∃` / `∧` / `↔` / `∨` (for constant terms such as `le_or_gt b 1`, the lemma's signature is instantiated with the arguments); the `·` bullet you hover in picks the case;
  - anonymous projections such as `hy.1`, `hy.2`;
  - in a `structure`, the fields declared above (`lo_lt_hi : lo < hi` with `lo : ℝ`); `set x := e with h`, `generalize e = x`, `∃! x, …`; a goal that is a `def … : Prop` of the PR is unfolded for `intro`, and `intro _` leaves an inaccessible name, as in Lean (`R✝`);
  - after `rw … at h` (also `nth_rw`, `erw`, `change … at h`), the type is replayed from the rewrite rules' statements; when a tactic that can't be replayed changes it (`simp at h`, `norm_num at h`, …), the type from before that tactic is shown, marked `-- outdated`.
- **Named arguments**: `(b := a)` shows the parameter `b` of the function being applied.

## How names are resolved

Lean Lens works from the text of the diff, the file at the PR's commit (fetched from `raw.githubusercontent.com`) and Loogle; it does not run Lean.

- **Dot notation** (`hl.nodup`, `(ContinuousAt.tendsto h).mono_left`, `hT.out.le`): the receiver's type is read from its binder, a file-level `variable`, a PR declaration, or a Loogle signature (conclusion plus argument substitution), step by step for longer chains. Bundled-map notations (`→ₗ[R]`, `≃+*`, `→ₘₛₗ[σ]`, ~60 in total) map to their structures.
- **Bare names** (`cons`, `pairwise_sort`): the `namespace` / `section` / `open` scope at the hovered line decides which candidates exist; root names and exported class fields (`mul_zero`, `star`) win over opened namespaces, then the current namespace. In a PR's own file, a name means that file's declaration in the current namespace first (`tprod` inside `namespace PiTensorProduct` is `PiTensorProduct.tprod`, not Mathlib's root `tprod`), unless it is `protected`, as Lean resolves names; and a declaration named exactly so wins over one whose last segment matches (`lift.tprod`).
- **Leading dots** (`:= .ofLinearMap …`): the namespace of the declaration's own type (`… ≃ₛₗ[σ] …` is `LinearEquiv`).
- **Scoped notations** for constants (`cexp`, `π`, `𝓝`, `ℝ≥0∞`, `d⁄dX`, `I`, `σ`, … about 70, read from Mathlib's `scoped notation` commands): the one in force at the line, by the file's `open`s (`open Real` makes `π` `Real.pi`, `open Nat.Prime` the prime-counting function).
- **The project's own types**: a section variable as receiver (`(T i).y₀` with `variable {T : ι → Rectangle}`) is typed from the file's `variable`s, and its field is found among the PR's declarations (`Rectangle.y₀`). For a field the type's own namespace doesn't have, a `def … : Prop` of the PR is unfolded, as Lean unfolds it: `(hsides i).imp` with `HasIntegerSide R := … ∨ …` is `Or.imp`.
- When several candidates remain, the tooltip lists them instead of guessing.
- Comments, docstring prose (except code in backticks), strings, attributes (also over several lines), universe names, section labels and `set_option` names are ignored. So is a Verso document (after `#doc (Manual) "…" =>`, as in a blueprint chapter), which is prose to the end of the file. Its `lean` code blocks are still code, and the names in `(lean := "A, B")` show their declarations.

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

The expected outputs of many cases are Lean's own hovers on the same code (mathlib4 PRs 45819 and 45909, and the closed PRs of [seewoo5/DifferentProofs](https://github.com/seewoo5/DifferentProofs), checked with lean-lsp).

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
│   ├── lean_tokenizer.js          # Name or term under the cursor, tactic position, notation
│   ├── lean_terms.js              # Term model: parser, printer, matching, universes, signatures
│   ├── binder_context.js          # Locals (written or inferred types), receivers, rewrite replay, page context
│   ├── term_hover.js              # Hovering inside a term: the term there and its type
│   ├── pr_scanner.js              # Declarations added in the PR, with the section variables they take
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
