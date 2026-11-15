# Lean Lens: Lean 4 Hover Inspector for GitHub

A Chrome extension for reviewing **Lean 4** pull requests on GitHub. Hover over an identifier, tactic or local variable in a diff and Lean Lens shows its type signature, docstring and where it comes from, without leaving the page.

It works on both GitHub diff views (the classic `/files` view and the newer `/changes` view) and on file pages.

Hovers come from two sources:

- **Estimated, with nothing to set up.** The extension reads the source, the PR's files and [Loogle](https://loogle.lean-lang.org/), and works out what Lean would show. This is what the sections below describe.
- **Lean's own output, with the local helper.** A small program on your machine has Lean run on the pull request you are reading, on your machine or in a GitHub Codespace of yours. Hovers are then exactly Lean's, and each tactic shows its proof state. See [Real Lean with the local helper](#real-lean-with-the-local-helper).

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

- **Dot notation** (`hl.nodup`, `(ContinuousAt.tendsto h).mono_left`, `hT.out.le`): the receiver's type is read from its binder, a file-level `variable`, a PR declaration, or a Loogle signature (conclusion plus argument substitution), step by step for longer chains. Bundled-map notations (`→ₗ[R]`, `≃+*`, `→ₘₛₗ[σ]`, ~60 in total) map to their structures. A field of a lemma shows what it says in its place, above the field's own statement: `Nat.even_add_one.mp {n : ℕ} : Even (n + 1) → ¬Even n` rather than `Iff.mp`'s `a → b`.
- **Bare names** (`cons`, `pairwise_sort`): the `namespace` / `section` / `open` scope at the hovered line decides which candidates exist; root names and exported class fields (`mul_zero`, `star`) win over opened namespaces, then the current namespace. In a PR's own file, a name means that file's declaration in the current namespace first (`tprod` inside `namespace PiTensorProduct` is `PiTensorProduct.tprod`, not Mathlib's root `tprod`), unless it is `protected`, as Lean resolves names; and a declaration named exactly so wins over one whose last segment matches (`lift.tprod`).
- **Leading dots** (`:= .ofLinearMap …`): the namespace of the declaration's own type (`… ≃ₛₗ[σ] …` is `LinearEquiv`).
- **Scoped notations** for constants (`cexp`, `π`, `𝓝`, `ℝ≥0∞`, `d⁄dX`, `I`, `σ`, … about 70, read from Mathlib's `scoped notation` commands): the one in force at the line, by the file's `open`s (`open Real` makes `π` `Real.pi`, `open Nat.Prime` the prime-counting function).
- **The project's own types**: a section variable as receiver (`(T i).y₀` with `variable {T : ι → Rectangle}`) is typed from the file's `variable`s, and its field is found among the PR's declarations (`Rectangle.y₀`). For a field the type's own namespace doesn't have, a `def … : Prop` of the PR is unfolded, as Lean unfolds it: `(hsides i).imp` with `HasIntegerSide R := … ∨ …` is `Or.imp`.
- When several candidates remain, the tooltip lists them instead of guessing.
- Comments, docstring prose (except code in backticks), strings, attributes (also over several lines), universe names, section labels and `set_option` names are ignored. So is a Verso document (after `#doc (Manual) "…" =>`, as in a blueprint chapter), which is prose to the end of the file. Its `lean` code blocks are still code, and the names in `(lean := "A, B")` show their declarations.

---

## Real Lean with the local helper

The helper runs Lean itself on the code you are reading, so nothing is estimated: a constant shows Lean's signature and docstring, a variable its type, a tactic its documentation, and inside a proof the tooltip adds the goals Lean recorded there. It works on any repository with a Lake project, and needs nothing from the repository.

```bash
node helper/lean-lens-helper.mjs
```

It prints an address and a token. Paste both into the extension's options, under **Real Lean**. Then, on a pull request, hover any name and press **Run Lean** in the tooltip. The first run on a project takes a while (see below); after that the results for the files of a commit are kept, and hovers on them are instant, with or without the project's build on disk.

What a hover shows once Lean has run:

- **Names and tactics**: what Lean recorded for the token, replacing the estimate.
- **Fields in their place**: Lean's hover on the `mp` of `Nat.even_add_one.mp` is `Iff.mp`'s general statement, `a → b`. The tooltip shows what it says there, `Nat.even_add_one.mp {n : ℕ} : Even (n + 1) → ¬Even n`, worked out from the hovers Lean recorded for the names before the dot, and keeps Lean's own hover below it. This works through chains (`hT.out.le : 0 ≤ T`) and for locals (`h.mp : p → q`).
- **Proof states**: on a tactic, the goals after it; on `by`, `·` and `| case =>`, the goals at that point. Hypotheses of one type share a line, as in Lean's infoview. A hover with a proof state is two columns: the state on the left, the definition on the right.
- **Messages**: Lean's errors, warnings and `#check` output at the hovered code.
- Where Lean recorded no hover (a gap between terms, a bracket), the estimate is shown and marked as estimated.

What the helper does for a repository, a commit and its Lean files:

1. Fetches the commit into its own folder. It never touches your checkouts.
2. Installs the Lean version the project pins, and downloads Mathlib's prebuilt cache if the project depends on Mathlib.
3. Builds what the files import, then elaborates each file with [SubVerso](https://github.com/leanprover/subverso), the library [Verso](https://verso.lean-lang.org/) uses to get this information.
4. Keeps the result for each file, and removes the copy and its build once they are not in use (see **Disk space**).

It needs Node 20 or later, `git`, and Lean's `elan` and `lake`.

**Reusing a checkout.** A Mathlib-based project takes about 10 GB and several minutes to prepare from nothing. If you already have the project built, link it, and the helper starts from a copy of your checkout and its build. On macOS the copy shares disk space with the original. On Linux it does where the file system can (Btrfs, XFS), and is a full copy otherwise.

```bash
node helper/lean-lens-helper.mjs --link seewoo5/DifferentProofs=$HOME/code/DifferentProofs
```

**Disk space.** Lean has to be on the machine that runs it. A Lean version is about 3 GB, and a project that uses Mathlib needs Mathlib's build, about 10 GB. The helper keeps as little of that as it can:

- What stays is the results (some hundred kilobytes for each Lean file), the SubVerso extractor (about 225 MB for each Lean version) and the settings.
- A repository's copy and its build are removed 30 minutes after its last run, and when the helper stops. If a helper was killed, the next one removes what it left. `--tidy-after MINUTES` changes the time (`0`: as soon as a run is over). `--keep-builds` keeps them, which saves the next run on that repository the copying or downloading.
- Mathlib's downloads (about 550 MB, compressed) go to a folder of the run and are deleted once unpacked. They do not go to your own `~/.cache/mathlib`.
- Lean versions are installed by `elan` and shared with your own projects. The helper notes the ones it installed itself.
- A project that uses Mathlib is not fetched when less than 12 GB is free.

```bash
node helper/lean-lens-helper.mjs clean
```

removes everything but the settings and the results, and uninstalls the Lean versions the helper installed. `clean --all` removes the results too.

The copy of a linked checkout shares its disk space with the original, so it costs far less than it looks: a 10.6 GB build copied this way took 0.3 GB of the disk. Tools that add up file sizes (`du`, the Finder) count it in full all the same.

**Lean in a codespace instead of on your machine.** Lean needs its files wherever it runs. With `--codespaces` that place is a [GitHub Codespace](https://github.com/features/codespaces) on your account, and your machine keeps only the results:

```bash
node helper/lean-lens-helper.mjs --codespaces
```

The extension is set up as before and talks to the same address.

- The first **Run Lean** on a repository creates a codespace on that repository (the smallest machine: 2 cores), installs Lean in it and starts this same helper there. Later runs use the same codespace, starting it again if it was stopped.
- The tooltip shows the run's progress as usual. The results are copied to your machine, so hovers keep working once the codespace has stopped. A hover never starts a codespace: only **Run Lean** does.
- A codespace is stopped 30 minutes after its last run and when the helper stops (`--tidy-after` changes the time, `--keep-codespaces` leaves them running). GitHub deletes one that goes unused for a week.
- A run goes on when the connection is lost, because your machine slept or its network changed: the helper in the codespace keeps working, and the helper here connects again and picks the run up. GitHub itself stops a codespace 30 minutes after the last connection to it, whatever is running in it, so during a run the helper connects every few minutes. A machine asleep for longer than that loses the run.
- `node helper/lean-lens-helper.mjs codespaces` lists the codespaces the helper made, with `--stop` it stops them and with `--delete` it deletes them. It leaves your other codespaces alone.

Your machine needs Node and GitHub's command line tool [`gh`](https://cli.github.com), signed in and allowed to use codespaces (`gh auth refresh -h github.com -s codespace`). It needs no Lean.

It is paid for from your own Codespaces allowance. A free account has 120 core-hours a month, which is 60 hours of this machine, and 15 GB-months of storage. Builds go to the codespace's temporary disk, which GitHub empties when the codespace stops, so a stopped one holds a Lean version (3 GB) and little else.

There is a codespace for each repository, and not one for everything, because GitHub's terms allow a codespace for developing or testing the repository it was started on.

**Safety.** Elaborating a Lean file runs the code in it, and `lake` runs the project's `lakefile`. So running Lean on a pull request means running that pull request's code on your machine.

- Lean never starts on its own. It runs when you press **Run Lean**, and only on repositories you have allowed (the button asks the first time; `--allow owner/repo` does it ahead).
- The helper listens on `127.0.0.1` only and answers only requests that carry its token. Requests from web pages are refused.
- **On macOS the project's code runs in a sandbox** (`lake`, and Lean elaborating a file). In it there is no network, except for the one step that fetches the project's dependencies and Mathlib's build. It cannot read your home folder, other volumes or the temporary folders: only system files, the Lean toolchain and the helper's copy of the project. It can write only inside that copy and the scratch folders of the run. It cannot write to the copy's `.git`, and it cannot move those folders or put something else in their place. It gets none of the helper's environment variables, and empty home and temporary folders that are deleted when the run is over.
- **On Linux it runs in a sandbox too**, made with [bubblewrap](https://github.com/containers/bubblewrap) when `bwrap` is installed and allowed to work. The code gets a file system of its own: the system folders and the Lean toolchain, read-only, and the helper's copy of the project and the scratch folders of the run. Nothing else exists for it. It has no network outside the fetching step, sees no process but its own, and gets the same clean environment. Without `bwrap` there is only the clean environment.
- **In a codespace** the pull request's code is not on your machine at all, and it runs in that Linux sandbox. That matters there too: a codespace holds a GitHub token that can push to the repository when you can, in a file any program in the codespace can read. If a codespace has no working sandbox and you can push to the repository, the run is refused unless the helper was started with `--no-sandbox`.
- The helper says which applies when it starts, and **Test Connection** in the options shows it.

The sandbox guards against the obvious; it is not a guarantee. On macOS it uses the system's `sandbox-exec` with rules that deny the things above and allow the rest (starting processes, reading system files). On Linux, bubblewrap builds the file system the code sees, which leaves it less; in the fetching step it shares the machine's network. `--no-sandbox` turns it off. That is needed when a project's dependencies are private repositories, because the sandbox has no git credentials.

A test file that tries to read a file in the home folder, write one there, fetch a URL, read an environment variable of the helper, plant a git hook, move the project's copy away and move its scratch home folder away is refused all seven in the sandbox. Without it the first five are allowed (the last two were not tried there: they would move real folders).

In a codespace, such a file tries eleven things: to read the codespace's GitHub token from its file, find it in the environment, read git's credential helper, the helper's own settings and a file in the home folder, write to the home folder and to the codespace's checkout, fetch a URL, plant a git hook, and move the project's copy and its scratch home folder away. All eleven are refused in the sandbox, where it sees three processes instead of fifteen. Without the sandbox, eight of the nine that were tried are allowed, reading the token's file among them.

**Measured** on an Apple M2 with Lean 4.35 and DifferentProofs linked: 78 seconds from an empty cache to the first file of a pull request. Of that, 28 seconds copy the checkout's build (10.6 GB), 25 build the SubVerso extractor (once for each Lean version), and the rest builds what the file imports and elaborates it. A further file takes 5 to 40 seconds. Removing the copy takes about 10 seconds. When Mathlib's build has to come from the network instead, it is 556 MB in about 9,000 files, which took 12 minutes on a connection giving 0.6 to 2 MB/s. The sandbox made no difference to that.

**Measured in a codespace** (2 cores, GitHub's default image, DifferentProofs): 6 minutes from nothing to the first result on this machine. Creating the codespace and starting the helper take half a minute, installing Lean one minute, fetching and unpacking Mathlib's build 3 to 5 minutes, and building the SubVerso extractor one minute. A stopped codespace takes about as long again: starting it takes half a minute, but its temporary disk is gone, and Mathlib's build with it. While it is up, a file takes what its imports take to build (2.5 minutes for all of DifferentProofs' own modules) and 5 to 45 seconds to elaborate. A run whose connection was cut on purpose in the middle finished all the same, and no later. The results are byte for byte those of the Mac.

**Limits**

- A tactic shows the goals after it, as Verso does, where Lean's infoview shows the goals before the tactic under the cursor. Hover the previous tactic (or `by`) for those.
- A tactic whose term contains another proof (`exact foo (by simp)`) has no state of its own: SubVerso records states on the innermost tactics only.
- SubVerso records the wrong goal on the `by` of `have h : T := by …`, so that `by` shows none. The `have` and the tactics inside it are right.
- A Verso document (`#doc … =>`) has no Lean hovers in its body.
- **Run Lean** on an added or unchanged line runs the pull request's Lean files. On a removed line it runs that one file at the base commit, which makes the helper switch commits and rebuild.
- A codespace of the smallest kind has two cores, and what Mathlib's cache does not cover is compiled there from source. DifferentProofs' blueprint chapters import Verso: building that was not finished after 28 minutes. `--codespace-machine standardLinux32gb` asks for four cores, which uses the allowance twice as fast.
- The Linux sandbox and the codespace route were tried in GitHub's default codespace image only (Ubuntu 24.04, bubblewrap 0.9), on a public repository. A repository whose own dev container has no SSH server cannot be set up this way, and the helper says so.
- Tested with Lean 4.35 only. SubVerso's output format is not stable, so the helper builds a pinned revision (`--subverso-rev` picks another), and it refuses output that does not reproduce the source text.

The same program can elaborate files without the extension, for example in a script. It removes the copy when it is done; with `--keep-builds` the next run starts from it.

```bash
node helper/lean-lens-helper.mjs run --repo owner/repo --sha <full commit hash> Path/To/File.lean
```

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

The helper's tests use `test/fixtures/Sample.subverso.json`, which is SubVerso's real output for `test/fixtures/Sample.lean`, so they need no Lean installation.

`test/demo_pr.html` is a static page that imitates a GitHub PR diff for trying tooltips offline.

---

## Project layout

```
chrome-lean-lens/
├── manifest.json                  # Manifest V3 configuration
├── icons/                         # Icons (generate_icons.py redraws them)
├── background/
│   ├── service_worker.js          # Loogle, file scope, tactic docs, caching, the helper's client
│   └── exact_data.js              # Reading Lean's own data: the token and proof state at a position
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
├── helper/
│   ├── lean-lens-helper.mjs       # The local helper: fetches a commit, runs Lean, serves the result
│   ├── codespaces.mjs             # Lean in a GitHub Codespace: the helper hands a run to itself there
│   └── convert.mjs                # SubVerso's output → hovers, proof states and messages by position
└── test/                          # Unit tests, fixtures and the demo page
```

## Options

Right-click the toolbar icon → **Options**:
- **Hover delay** (default 250 ms)
- **PR declaration scanner**, **Loogle lookups**, **built-in tactic docs**: on/off
- **Theme**: match GitHub, Slate Dark, or Clean Light
- **Real Lean**: use the local helper, with its address and token

The helper replaces the companion server of earlier versions, which searched a project's files by name without running Lean.
