/**
 * Built-in Lean 4 & Mathlib reference database.
 * Provides instantaneous, zero-latency docstrings and signatures for
 * core tactics, standard library types, and keywords.
 */

(function () {
  const LEAN_BUILTINS = {
    // === TACTICS ===
    "simp": {
      name: "simp",
      kind: "tactic",
      module: "Lean.Elab.Tactic.Simp",
      typeSignature: "simp [lemma1, lemma2, ← lemma3] (at h)?",
      docstring: `The **simplifier** rewrites subexpressions using conditional equational theorems and reduction rules tagged with the \`@[simp]\` attribute.

**Usage:**
- \`simp\`: Simplify current goal.
- \`simp [h1, h2]\`: Simplify using additional lemmas \`h1\`, \`h2\`.
- \`simp [← h]\`: Rewrite in reverse direction using \`h\`.
- \`simp [-h]\`: Temporarily disable simplification rule \`h\`.
- \`simp only [h1, h2]\`: Use *only* the specified lemmas, ignoring global simp set.
- \`simp at h\`: Simplify hypothesis \`h\` instead of the target goal.
- \`simp at *\`: Simplify all hypotheses and the goal.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/Simp.html",
      source: "builtin"
    },
    "rw": {
      name: "rw",
      kind: "tactic",
      module: "Lean.Elab.Tactic.Rewrite",
      typeSignature: "rw [h1, ← h2] (at loc)?",
      docstring: `**Rewrite** target or hypotheses using equalities, equivalences, or bi-implications.

**Usage:**
- \`rw [h]\`: Rewrites the first matching subterm in the goal with the right-hand side of \`h\`.
- \`rw [← h]\`: Rewrites using \`h\` from right to left.
- \`rw [h1, h2]\`: Sequences multiple rewrites.
- \`rw [h] at h2\`: Rewrites inside hypothesis \`h2\`.
- Automatically calls \`try rfl\` after rewriting.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/Rewrite.html",
      source: "builtin"
    },
    "rewrite": {
      name: "rewrite",
      kind: "tactic",
      module: "Lean.Elab.Tactic.Rewrite",
      typeSignature: "rewrite [h1, ← h2] (at loc)?",
      docstring: `Identical to \`rw\`, but does not attempt to close the goal with \`rfl\` automatically.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/Rewrite.html",
      source: "builtin"
    },
    "apply": {
      name: "apply",
      kind: "tactic",
      module: "Lean.Elab.Tactic.Basic",
      typeSignature: "apply e",
      docstring: `Unifies the target goal with the conclusion of the expression \`e\`, creating new subgoals for each argument of \`e\` that was not solved by unification.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/Basic.html",
      source: "builtin"
    },
    "exact": {
      name: "exact",
      kind: "tactic",
      module: "Lean.Elab.Tactic.Basic",
      typeSignature: "exact e",
      docstring: `Closes the current goal by providing an exact proof term \`e\` whose type is definitionally equal to the goal type.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/Basic.html",
      source: "builtin"
    },
    "intro": {
      name: "intro",
      kind: "tactic",
      module: "Lean.Elab.Tactic.Basic",
      typeSignature: "intro x y ...",
      docstring: `Introduces universally quantified variables (\`∀\`) or hypothesis premises (\`→\`) from the goal into the local context.

**Usage:**
- \`intro x\`: introduces one variable or hypothesis with name \`x\`.
- \`intro x y z\`: introduces three successive binders.
- \`intro (x : α)\`: introduces with explicit type checking.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/Basic.html",
      source: "builtin"
    },
    "intros": {
      name: "intros",
      kind: "tactic",
      module: "Lean.Elab.Tactic.Basic",
      typeSignature: "intros x y ...",
      docstring: `Repeatedly introduces binders into the local context. Without arguments, introduces as many as possible with generated names.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/Basic.html",
      source: "builtin"
    },
    "rfl": {
      name: "rfl",
      kind: "tactic",
      module: "Lean.Elab.Tactic.Basic",
      typeSignature: "rfl",
      docstring: `Closes a goal of the form \`a = b\`, \`HEq a b\`, or any relation registered with \`@[refl]\`, if \`a\` and \`b\` are definitionally equal.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/Basic.html",
      source: "builtin"
    },
    "cases": {
      name: "cases",
      kind: "tactic",
      module: "Lean.Elab.Tactic.Basic",
      typeSignature: "cases e (with | c1 x => ... | c2 y => ...)?",
      docstring: `Performs case analysis on an inductive type or hypothesis \`e\`. Generates one subgoal for each constructor of \`e\`'s type.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/Basic.html",
      source: "builtin"
    },
    "rcases": {
      name: "rcases",
      kind: "tactic",
      module: "Mathlib.Tactic.RCases",
      typeSignature: "rcases e with ⟨x, y, z⟩ | ⟨a, b⟩",
      docstring: `**Recursive case analysis** / destructuring on terms and hypotheses according to a pattern.

**Usage:**
- \`rcases h with ⟨x, y⟩\`: Destructures a conjunction or existential \`h\`.
- \`rcases h with h1 | h2\`: Case splits on a disjunction (\`Or\`).`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/RCases.html",
      source: "builtin"
    },
    "obtain": {
      name: "obtain",
      kind: "tactic",
      module: "Mathlib.Tactic.RCases",
      typeSignature: "obtain ⟨x, hx⟩ : ∃ x, P x := proof",
      docstring: `Binds an existential witness and hypothesis from a proof term or current goal, combining \`have\` with \`rcases\` pattern destructuring.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/RCases.html",
      source: "builtin"
    },
    "induction": {
      name: "induction",
      kind: "tactic",
      module: "Lean.Elab.Tactic.Induction",
      typeSignature: "induction n (with | zero => ... | succ n ih => ...)?",
      docstring: `Performs mathematical or structural induction on a term \`n\` of an inductive type (such as \`Nat\`, \`List\`, etc.), providing induction hypotheses for recursive constructors.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/Induction.html",
      source: "builtin"
    },
    "have": {
      name: "have",
      kind: "tactic",
      module: "Lean.Elab.Tactic.Basic",
      typeSignature: "have h : P := proof",
      docstring: `Introduces a new intermediate lemma or hypothesis \`h : P\` into the local context. Subgoals are created if proof is omitted.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/Basic.html",
      source: "builtin"
    },
    "let": {
      name: "let",
      kind: "tactic",
      module: "Lean.Elab.Tactic.Basic",
      typeSignature: "let x : T := val",
      docstring: `Introduces a local definition \`x\` with value \`val\` into the context. Unlike \`have\`, \`let\` preserves the computational equality \`x = val\`.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/Basic.html",
      source: "builtin"
    },
    "suffices": {
      name: "suffices",
      kind: "tactic",
      module: "Lean.Elab.Tactic.Basic",
      typeSignature: "suffices h : P by ...",
      docstring: `Declares that proving \`P\` is sufficient to prove the current goal, replacing the current goal with \`P\` and creating a secondary goal to show \`P → CurrentGoal\`.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/Basic.html",
      source: "builtin"
    },
    "ext": {
      name: "ext",
      kind: "tactic",
      module: "Mathlib.Tactic.Ext",
      typeSignature: "ext x y ...",
      docstring: `Applies **extensionality lemmas** to prove that two complex structures, functions, or sets are equal if their components or values on all points are equal (e.g. \`f = g ↔ ∀ x, f x = g x\`).`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Ext.html",
      source: "builtin"
    },
    "ring": {
      name: "ring",
      kind: "tactic",
      module: "Mathlib.Tactic.Ring",
      typeSignature: "ring",
      docstring: `Proves identities in commutative (semi)rings by putting expressions into a normal polynomial form. Works over \`ℕ\`, \`ℤ\`, \`ℚ\`, \`ℝ\`, \`ℂ\`, polynomial rings, etc.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Ring.html",
      source: "builtin"
    },
    "linarith": {
      name: "linarith",
      kind: "tactic",
      module: "Mathlib.Tactic.Linarith",
      typeSignature: "linarith (only [h1, h2])?",
      docstring: `**Linear arithmetic solver**: finds contradictions or proves equalities/inequalities among linear equations using Fourier-Motzkin elimination.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Linarith.html",
      source: "builtin"
    },
    "omega": {
      name: "omega",
      kind: "tactic",
      module: "Lean.Elab.Tactic.Omega",
      typeSignature: "omega",
      docstring: `Decision procedure for **Presburger arithmetic** over integers (\`Int\`) and natural numbers (\`Nat\`). Solves linear integer constraints with quantifiers, addition, subtraction, and multiplication by constants.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/Omega.html",
      source: "builtin"
    },
    "norm_num": {
      name: "norm_num",
      kind: "tactic",
      module: "Mathlib.Tactic.NormNum",
      typeSignature: "norm_num (at loc)?",
      docstring: `Normalizes numerical expressions and calculates explicit numerical values/inequalities (e.g., \`2 + 2 = 4\`, \`17 < 34\`, prime tests).`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/NormNum.html",
      source: "builtin"
    },
    "positivity": {
      name: "positivity",
      kind: "tactic",
      module: "Mathlib.Tactic.Positivity",
      typeSignature: "positivity",
      docstring: `Proves that an expression is positive (\`0 < x\`), non-negative (\`0 ≤ x\`), or non-zero (\`x ≠ 0\`) by analyzing the signs of its constituent operations.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Positivity.html",
      source: "builtin"
    },
    "gcongr": {
      name: "gcongr",
      kind: "tactic",
      module: "Mathlib.Tactic.GCongr",
      typeSignature: "gcongr",
      docstring: `**Generalized congruence**: simplifies goals involving relations (\`=\`, \`≤\`, \`<\`) by stripping common monotone functions and matching arguments pairwise.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/GCongr.html",
      source: "builtin"
    },
    "aesop": {
      name: "aesop",
      kind: "tactic",
      module: "Aesop",
      typeSignature: "aesop (add safe ...)?",
      docstring: `**Automated Extensible Search for Obvious Proofs**: white-box best-first proof search using rule sets of simplification, safe introductions, and backtracking branches.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Aesop.html",
      source: "builtin"
    },
    "tauto": {
      name: "tauto",
      kind: "tactic",
      module: "Mathlib.Tactic.Tauto",
      typeSignature: "tauto",
      docstring: `Closes goals that are propositional tautologies (intuitionistic or classical logic over \`∧\`, \`∨\`, \`¬\`, \`→\`, \`↔\`, \`True\`, \`False\`).`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Tauto.html",
      source: "builtin"
    },
    "assumption": {
      name: "assumption",
      kind: "tactic",
      module: "Lean.Elab.Tactic.Basic",
      typeSignature: "assumption",
      docstring: `Looks for an hypothesis in the local context whose type unifies with the current goal, and applies it to close the goal.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/Basic.html",
      source: "builtin"
    },
    "contradiction": {
      name: "contradiction",
      kind: "tactic",
      module: "Lean.Elab.Tactic.Basic",
      typeSignature: "contradiction",
      docstring: `Closes the goal if the local context contains contradictory hypotheses (e.g. \`h : False\`, \`h1 : P\` and \`h2 : ¬P\`, or distinct constructors of an inductive type equal to each other).`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/Basic.html",
      source: "builtin"
    },
    "constructor": {
      name: "constructor",
      kind: "tactic",
      module: "Lean.Elab.Tactic.Basic",
      typeSignature: "constructor",
      docstring: `Applies the first applicable constructor of the inductive datatype of the goal (e.g., splits an \`And\` or \`Iff\` goal into two subgoals).`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/Basic.html",
      source: "builtin"
    },
    "funext": {
      name: "funext",
      kind: "tactic",
      module: "Lean.Elab.Tactic.Basic",
      typeSignature: "funext x y ...",
      docstring: `Applies functional extensionality to prove equality between functions: reduces \`f = g\` to \`∀ x, f x = g x\`.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/Basic.html",
      source: "builtin"
    },
    "calc": {
      name: "calc",
      kind: "tactic",
      module: "Lean.Elab.Calc",
      typeSignature: "calc a = b := ... \\n   _ = c := ...",
      docstring: `Calculational proof mode for chaining transitive relations (like \`=\`, \`≤\`, \`<\`) step by step.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Calc.html",
      source: "builtin"
    },
    "dsimp": {
      name: "dsimp",
      kind: "tactic",
      module: "Lean.Elab.Tactic.Simp",
      typeSignature: "dsimp (at loc)?",
      docstring: `**Definitional simplifier**: simplifies expressions only using definitional equalities, without altering the term structure or creating equality proof witnesses.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/Simp.html",
      source: "builtin"
    },
    "unfold": {
      name: "unfold",
      kind: "tactic",
      module: "Lean.Elab.Tactic.Basic",
      typeSignature: "unfold f (at loc)?",
      docstring: `Unfolds the definition of a specific function or constant \`f\` using its defining equations.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/Basic.html",
      source: "builtin"
    },
    "split": {
      name: "split",
      kind: "tactic",
      module: "Lean.Elab.Tactic.Split",
      typeSignature: "split (at loc)?",
      docstring: `Splits target or hypothesis containing \`if ... then ... else\` or pattern match \`match ... with\` into separate branches.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/Split.html",
      source: "builtin"
    },
    "sorry": {
      name: "sorry",
      kind: "tactic",
      module: "Init.Core",
      typeSignature: "sorry",
      docstring: `A placeholder / cheat tactic that closes any goal unconditionally with an axiom, producing a compiler warning. Used during development to sketch proofs.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Init/Core.html",
      source: "builtin"
    },

    // === CORE TYPES & CONSTANTS ===
    "Nat": {
      name: "Nat",
      kind: "inductive",
      module: "Init.Prelude",
      typeSignature: "inductive Nat : Type\\n| zero : Nat\\n| succ (n : Nat) : Nat",
      docstring: `The type of **natural numbers** (non-negative integers: \`0, 1, 2, ...\`), defined inductively as Peano numbers. Supports arbitrary-precision arithmetic at runtime.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Nat",
      source: "builtin"
    },
    "Int": {
      name: "Int",
      kind: "inductive",
      module: "Init.Data.Int.Basic",
      typeSignature: "inductive Int : Type\\n| ofNat (n : Nat) : Int\\n| negSucc (n : Nat) : Int",
      docstring: `The type of **integers** (\`..., -2, -1, 0, 1, 2, ...\`), represented by natural numbers and negative successor offsets.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Init/Data/Int/Basic.html#Int",
      source: "builtin"
    },
    "Real": {
      name: "Real",
      kind: "def",
      module: "Mathlib.Data.Real.Basic",
      typeSignature: "def Real : Type",
      docstring: `The type of **real numbers** \`ℝ\`, defined as the completion of Cauchy sequences of rational numbers (\`ℚ\`). Notation: \`ℝ\`.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Real/Basic.html#Real",
      source: "builtin"
    },
    "Complex": {
      name: "Complex",
      kind: "structure",
      module: "Mathlib.Data.Complex.Basic",
      typeSignature: "structure Complex : Type where\\n  re : ℝ\\n  im : ℝ",
      docstring: `The type of **complex numbers** \`ℂ\`, represented as a pair of real numbers (real and imaginary parts). Notation: \`ℂ\`.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Complex/Basic.html#Complex",
      source: "builtin"
    },
    "List": {
      name: "List",
      kind: "inductive",
      module: "Init.Prelude",
      typeSignature: "inductive List (α : Type u) : Type u\\n| nil : List α\\n| cons (head : α) (tail : List α) : List α",
      docstring: `Finite linked lists of elements of type \`α\`. Standard functional list structure with \`[]\` and \`x :: xs\` constructors.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#List",
      source: "builtin"
    },
    "Array": {
      name: "Array",
      kind: "structure",
      module: "Init.Prelude",
      typeSignature: "structure Array (α : Type u) : Type u",
      docstring: `Dynamically sized array backed by a contiguous memory buffer. Provides \(O(1)\) index lookups and linear destructive updates when unshared.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Array",
      source: "builtin"
    },
    "Option": {
      name: "Option",
      kind: "inductive",
      module: "Init.Prelude",
      typeSignature: "inductive Option (α : Type u) : Type u\\n| none : Option α\\n| some (val : α) : Option α",
      docstring: `Represents an optional value: either \`some a\` containing a value of type \`α\`, or \`none\` representing absence.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Option",
      source: "builtin"
    },
    "Finset": {
      name: "Finset",
      kind: "structure",
      module: "Mathlib.Data.Finset.Basic",
      typeSignature: "structure Finset (α : Type u) : Type u where\\n  val : Multiset α\\n  nodup : Multiset.Nodup val",
      docstring: `The type of **finite sets** with elements of type \`α\`, represented as a multiset without duplicates. Supports decisive membership (\`x ∈ s\`) and finite operations (sum, prod, card).`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Basic.html#Finset",
      source: "builtin"
    },
    "Set": {
      name: "Set",
      kind: "def",
      module: "Mathlib.Data.Set.Basic",
      typeSignature: "def Set (α : Type u) : Type u := α → Prop",
      docstring: `The type of sets of elements of type \`α\`, identified with characteristic predicates \`α → Prop\`.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Basic.html#Set",
      source: "builtin"
    },
    "Continuous": {
      name: "Continuous",
      kind: "def",
      module: "Mathlib.Topology.Basic",
      typeSignature: "def Continuous [TopologicalSpace α] [TopologicalSpace β] (f : α → β) : Prop",
      docstring: `A function \`f : α → β\` between topological spaces is **continuous** if the preimage of every open set in \`β\` is open in \`α\`.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Basic.html#Continuous",
      source: "builtin"
    },
    "TopologicalSpace": {
      name: "TopologicalSpace",
      kind: "class",
      module: "Mathlib.Topology.Basic",
      typeSignature: "class TopologicalSpace (α : Type u) : Type u",
      docstring: `Typeclass defining a **topology** on a set \`α\`, specifying which subsets are considered open and satisfying the axioms of topology.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Basic.html#TopologicalSpace",
      source: "builtin"
    },
    "Finset.sum": {
      name: "Finset.sum",
      kind: "def",
      module: "Mathlib.Algebra.BigOperators.Group.Finset",
      typeSignature: "def Finset.sum [AddCommMonoid β] (s : Finset α) (f : α → β) : β",
      docstring: `Sum of a function \`f\` evaluated over all elements of a finite set \`s\`: \`∑ x ∈ s, f x\`.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Group/Finset.html#Finset.sum",
      source: "builtin"
    },
    "List.map": {
      name: "List.map",
      kind: "def",
      module: "Init.Data.List.Basic",
      typeSignature: "def List.map (f : α → β) : List α → List β",
      docstring: `Applies function \`f\` to each element in a list, returning the resulting list.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/Basic.html#List.map",
      source: "builtin"
    },
    "Subtype": {
      name: "Subtype",
      kind: "structure",
      module: "Init.Prelude",
      typeSignature: "structure Subtype {α : Sort u} (p : α → Prop) : Sort (max 1 u) where\\n  val : α\\n  property : p val",
      docstring: `A subtype \`{x : α // p x}\` pairs an underlying value \`x\` with a mathematical proof that \`x\` satisfies predicate \`p\`.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Subtype",
      source: "builtin"
    },
    "Decidable": {
      name: "Decidable",
      kind: "class",
      module: "Init.Prelude",
      typeSignature: "class inductive Decidable (p : Prop) : Type\\n| isFalse (h : ¬p) : Decidable p\\n| isTrue (h : p) : Decidable p",
      docstring: `Evidence that a proposition \`p\` is algorithmically decidable as either definitely true or definitely false, enabling \`if p then ... else ...\`.`,
      sourceUrl: "https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Decidable",
      source: "builtin"
    },
    // === TERM SYNTAX AND COMMANDS ===
    "mod_cast": {
      name: "mod_cast",
      kind: "syntax",
      module: "Lean.Elab.Tactic.NormCast",
      typeSignature: "mod_cast e",
      docstring: "Term syntax: normalizes the casts (`↑`) in the expected type and in the type of `e`, as `norm_cast` does, and then uses `e` (like `exact_mod_cast e` in tactic mode)."
    },
    "guard_msgs": {
      name: "#guard_msgs",
      kind: "command",
      module: "Lean.Elab.GuardMsgs",
      typeSignature: "#guard_msgs (drop? info|warning|error|all)? in command",
      docstring: "Runs the command after `in` and checks that the messages it logs are exactly the ones written in the doc comment before `#guard_msgs` (`/-- info: … -/`); a mismatch is an error. Used for tests."
    }
  };
  Object.setPrototypeOf(LEAN_BUILTINS, null); // looked up by words from the source: no `constructor`, `toString`, … from Object

  window.VersoBuiltins = {
    get(token) {
      if (!token) return null;
      if (LEAN_BUILTINS[token]) return LEAN_BUILTINS[token];
      // Try suffix or case insensitive match if applicable
      const direct = LEAN_BUILTINS[token];
      if (direct) return direct;
      // Search by exact name
      for (const key of Object.keys(LEAN_BUILTINS)) {
        if (key.toLowerCase() === token.toLowerCase()) {
          return LEAN_BUILTINS[key];
        }
      }
      return null;
    },
    has(token) {
      return Boolean(this.get(token));
    },
    getAll() {
      return LEAN_BUILTINS;
    }
  };
})();
