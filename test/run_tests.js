/**
 * Automated test suite for the Lean Lens Chrome extension.
 * Tests tokenizer, PR diff scanner, builtins database, and HTML rendering.
 */

const assert = require('assert');
const fs = require('fs');
const path = require('path');
const vm = require('vm');

console.log("=== Running Lean Lens Test Suite ===\n");

// Setup minimal DOM simulation in VM context
const context = {
  console: console,
  addEventListener: () => {},
  document: {},
  Node: { TEXT_NODE: 3, ELEMENT_NODE: 1 },
  setTimeout: setTimeout,
  clearTimeout: clearTimeout,
  Date: Date
};
context.window = context;

function loadScript(relPath) {
  const fullPath = path.join(__dirname, '..', relPath);
  const code = fs.readFileSync(fullPath, 'utf8');
  vm.runInNewContext(code, context);
}

// 1. Test Builtins Database
console.log("1. Testing Builtins Database...");
loadScript('content/builtins_db.js');
const builtins = context.VersoBuiltins;
assert(builtins, "VersoBuiltins should be defined");

// Test tactics
const simp = builtins.get("simp");
assert(simp && simp.kind === "tactic", "simp should be recognized as tactic");
assert(simp.docstring.includes("simplifier"), "simp docstring should be detailed");

const rw = builtins.get("rw");
assert(rw && rw.kind === "tactic", "rw should be recognized as tactic");

const omega = builtins.get("omega");
assert(omega && omega.kind === "tactic", "omega should be recognized as tactic");

// Test types
const nat = builtins.get("Nat");
assert(nat && nat.kind === "inductive", "Nat should be recognized as inductive type");

const finsetSum = builtins.get("Finset.sum");
assert(finsetSum && finsetSum.name === "Finset.sum", "Finset.sum should be found");

// Builtins should NOT contain arbitrary Mathlib domain definitions (they should be resolved dynamically)
assert(!builtins.get("ZeroAtFilter"), "ZeroAtFilter should NOT be hardcoded into builtins");
assert(!builtins.get("BoundedAtFilter"), "BoundedAtFilter should NOT be hardcoded into builtins");

console.log("   ✓ Builtins DB verified: contains only core tactics and prelude primitives.\n");

// 2. Test Tokenizer Logic
console.log("2. Testing Lean Tokenizer...");
loadScript('content/lean_tokenizer.js');
const tokenizer = context.LeanTokenizer;
assert(tokenizer, "LeanTokenizer should be defined");

function mockTextNode(text) {
  return {
    nodeType: 3,
    nodeValue: text
  };
}

// Extract simple token
const res1 = tokenizer.extractTokenAt(mockTextNode("lemma continuous_extend_dense (hd : Dense s)"), 8);
assert(res1 && res1.token === "continuous_extend_dense", `Expected continuous_extend_dense, got ${res1?.token}`);

// Extract dotted token
const res2 = tokenizer.extractTokenAt(mockTextNode("  Finset.sum s (fun i => f i)"), 4);
assert(res2 && res2.token === "Finset", `Expected Finset, got ${res2?.token}`);
assert(res2.subToken === "Finset", `Expected subToken Finset, got ${res2.subToken}`);

const res3 = tokenizer.extractTokenAt(mockTextNode("  Finset.sum s (fun i => f i)"), 11);
assert(res3 && res3.token === "Finset.sum", `Expected Finset.sum, got ${res3?.token}`);
assert(res3.subToken === "sum", `Expected subToken sum, got ${res3.subToken}`);

// Reject pure number
const resNum = tokenizer.extractTokenAt(mockTextNode("  have h : 12345 = 12345 := rfl"), 13);
assert(resNum === null, "Pure numbers should return null");

// Token with prime
const resPrime = tokenizer.extractTokenAt(mockTextNode("  have h' : x' = y' := rfl"), 9);
assert(resPrime && resPrime.token === "h'", `Expected h', got ${resPrime?.token}`);

// Extract token from full line across dots
const lineSnippet = "  lemma foo (h : FunctionsBoundedAtImInfty.easy_lemma f)";
// Index 25 is on "FunctionsBoundedAtImInfty"
const tokenNamespace = tokenizer.extractTokenFromLine(lineSnippet, 25);
assert(tokenNamespace && tokenNamespace.token === "FunctionsBoundedAtImInfty",
  `Expected FunctionsBoundedAtImInfty, got ${tokenNamespace?.token}`);

// Index 45 is on "easy_lemma"
const tokenLemma = tokenizer.extractTokenFromLine(lineSnippet, 45);
assert(tokenLemma && tokenLemma.token === "FunctionsBoundedAtImInfty.easy_lemma",
  `Expected FunctionsBoundedAtImInfty.easy_lemma, got ${tokenLemma?.token}`);

// Test fine-grained token extraction on dot chains (ZeroAtFilter.neg)
const dotLine = "  exact ZeroAtFilter.neg h";
// Hovering over "ZeroAtFilter" (index 12)
const hoverBase = tokenizer.extractTokenFromLine(dotLine, 12);
assert(hoverBase && hoverBase.token === "ZeroAtFilter", `Expected ZeroAtFilter, got ${hoverBase?.token}`);
assert(hoverBase.subToken === "ZeroAtFilter", `Expected subToken ZeroAtFilter, got ${hoverBase?.subToken}`);

// Hovering over "neg" (index 22)
const hoverLemma = tokenizer.extractTokenFromLine(dotLine, 22);
assert(hoverLemma && hoverLemma.token === "ZeroAtFilter.neg", `Expected ZeroAtFilter.neg, got ${hoverLemma?.token}`);
assert(hoverLemma.subToken === "neg", `Expected subToken neg, got ${hoverLemma?.subToken}`);

console.log("   ✓ Tokenizer verified: extracts simple, dotted, and fine-grained chain tokens.\n");

// 3. Test PR Scanner Logic
console.log("3. Testing PR Scanner Regex & Declaration Parser...");
loadScript('content/pr_scanner.js');
const prScanner = context.LeanPRScanner;
assert(prScanner, "LeanPRScanner should be defined");

// Mock container with rows
const mockRows = [
  { textContent: "+/-- Extension lemma for continuous maps on dense subspaces. -/", classList: { contains: () => false }, getAttribute: () => null },
  { textContent: "+lemma continuous_extend_dense (hd : Dense s) (hf : Continuous f) : Continuous (Dense.extend hd f) := by", classList: { contains: () => false }, getAttribute: () => "123" },
  { textContent: "+  intro x", classList: { contains: () => false }, getAttribute: () => "124" },
  { textContent: "+/-- Lift a dense subspace homomorphism. -/", classList: { contains: () => false }, getAttribute: () => null },
  { textContent: "+def DenseSubspace.lift (s : Finset Nat) : Real :=", classList: { contains: () => false }, getAttribute: () => "46" }
];

const mockContainer = {
  querySelectorAll: (selector) => mockRows
};

prScanner.scanDiffLines(mockContainer, "Mathlib/Topology/Maps.lean");

const foundLemma = prScanner.find("continuous_extend_dense");
assert(foundLemma, "PR scanner should find continuous_extend_dense");
assert(foundLemma.kind === "lemma", `Expected kind lemma, got ${foundLemma.kind}`);
assert(foundLemma.docstring.includes("Extension lemma"), `Docstring mismatch: ${foundLemma.docstring}`);
assert(foundLemma.lineNumber === 123, `Line number mismatch: ${foundLemma.lineNumber}`);

const foundDef = prScanner.find("DenseSubspace.lift");
assert(foundDef, "PR scanner should find DenseSubspace.lift");
assert(foundDef.kind === "def", `Expected kind def, got ${foundDef.kind}`);
assert(foundDef.docstring.includes("Lift a dense subspace"), `Docstring mismatch: ${foundDef.docstring}`);

console.log("   ✓ PR Scanner verified: successfully parses PR declarations, kinds, and docstrings.\n");

// 4. Test Lean Syntax Highlighter
console.log("4. Testing Lean Syntax Highlighter (highlightLean)...");
// Create mock DOM elements for tooltip_view
context.document.getElementById = () => null;
context.document.createElement = () => ({
  addEventListener: () => {},
  querySelector: () => ({ addEventListener: () => {} }),
  querySelectorAll: () => []
});
context.document.body = { appendChild: () => {} };

loadScript('content/tooltip_view.js');
const tooltipView = context.VersoTooltipView;
assert(tooltipView, "VersoTooltipView should be defined");

// Test the exact snippet from user's report
const testSig = "def Continuous [TopologicalSpace α] [TopologicalSpace β] (f : α → β) : Prop";
const highlighted = tooltipView.highlightLean(testSig);

console.log("   Highlighted output:", highlighted);
assert(!highlighted.startsWith('="v-kw">'), `Bug detected! Starts with plain text ="v-kw">: ${highlighted}`);
assert(!highlighted.includes('<span class<span'), `Bug detected! Nested broken span tags found: ${highlighted}`);
assert(highlighted.includes('<span class="v-kw">def</span>'), "def should be wrapped in valid v-kw span");
assert(highlighted.includes('<span class="v-inst">[TopologicalSpace α]</span>'), "Instance argument should be wrapped in v-inst span");
assert(highlighted.includes('<span class="v-sym">:</span>'), "Colon should be wrapped in v-sym span");
assert(highlighted.includes('<span class="v-sym">→</span>'), "Arrow should be wrapped in v-sym span");

console.log("   ✓ Syntax Highlighter verified: perfectly renders Lean keywords, binders, and symbols.\n");

// 5. Test Loogle Dynamic Hit Selection
console.log("5. Testing Dynamic Loogle Hit Resolution...");
const mockLoogleHits = [
  { name: "Filter.ZeroAtFilter.neg", type: "lemma ...", module: "Mathlib.Order.Filter.ZeroAndBoundedAtFilter" },
  { name: "Filter.ZeroAtFilter", type: "def Filter.ZeroAtFilter ...", module: "Mathlib.Order.Filter.ZeroAndBoundedAtFilter" },
  { name: "Filter.ZeroAtFilter.add", type: "lemma ...", module: "Mathlib.Order.Filter.ZeroAndBoundedAtFilter" },
  { name: "Filter.BoundedAtFilter", type: "def Filter.BoundedAtFilter ...", module: "Mathlib.Order.Filter.ZeroAndBoundedAtFilter" }
];

// Load the real selection logic from the service worker (stubbing the chrome API).
context.chrome = {
  runtime: { onMessage: { addListener: () => {} } },
  storage: { local: { get: () => {}, set: () => {}, clear: () => {} } }
};
loadScript('background/service_worker.js');
const selectLoogleHit = context.selectLoogleHit;
assert(typeof selectLoogleHit === "function", "selectLoogleHit should be defined by service_worker.js");

const resolvedZero = selectLoogleHit(mockLoogleHits, "ZeroAtFilter", "ZeroAtFilter").hit;
assert(resolvedZero.name === "Filter.ZeroAtFilter", `Expected Filter.ZeroAtFilter, got ${resolvedZero?.name}`);

const resolvedNeg = selectLoogleHit(mockLoogleHits, "ZeroAtFilter.neg", "neg").hit;
assert(resolvedNeg.name === "Filter.ZeroAtFilter.neg", `Expected Filter.ZeroAtFilter.neg, got ${resolvedNeg?.name}`);

const resolvedBounded = selectLoogleHit(mockLoogleHits, "BoundedAtFilter", "BoundedAtFilter").hit;
assert(resolvedBounded.name === "Filter.BoundedAtFilter", `Expected Filter.BoundedAtFilter, got ${resolvedBounded?.name}`);

// Regression: mathlib4#45928, `hl.sortedLE.pairwise` must not resolve to List.Perm.pairwise.
const pairwiseHits = [
  { name: "List.Pairwise" },
  { name: "List.Perm.pairwise" },
  { name: "Array.Perm.pairwise" },
  { name: "List.IsChain.pairwise" },
  { name: "List.SortedLE.pairwise" },
  { name: "List.SortedGE.pairwise" }
];
const sortedLE = selectLoogleHit(pairwiseHits, "sortedLE.pairwise", "pairwise");
assert(sortedLE && sortedLE.hit && sortedLE.hit.name === "List.SortedLE.pairwise",
  `Expected List.SortedLE.pairwise, got ${JSON.stringify(sortedLE)}`);

// If the qualifier matches nothing in the hit list, never pick an arbitrary `.pairwise`.
const noQualifier = selectLoogleHit(pairwiseHits.filter(h => h.name !== "List.SortedLE.pairwise"), "sortedLE.pairwise", "pairwise");
assert(noQualifier && !noQualifier.hit && noQualifier.candidates.length === 4,
  `Expected 4 ambiguous candidates, got ${JSON.stringify(noQualifier)}`);

// Bare token with several suffix matches is ambiguous, not a guess.
const barePairwise = selectLoogleHit(pairwiseHits, "pairwise", "pairwise");
assert(barePairwise && !barePairwise.hit && barePairwise.candidates.length === 5,
  `Expected bare pairwise to be ambiguous, got ${JSON.stringify(barePairwise)}`);

// Case matters for the last segment: `Pairwise` is not `pairwise`.
const pascal = selectLoogleHit(pairwiseHits, "Pairwise", "Pairwise");
assert(pascal && pascal.hit && pascal.hit.name === "List.Pairwise", `Expected List.Pairwise, got ${JSON.stringify(pascal)}`);

// No relevant hit at all → null (previously fell back to hits[0]).
assert(selectLoogleHit(mockLoogleHits, "Continuous", "Continuous") === null, "Unrelated hits should give null");

const amb = context.buildAmbiguousResult("sortedLE.pairwise", noQualifier.candidates);
assert(amb.ambiguous && amb.name === "pairwise" && amb.docstring.includes("List.Perm.pairwise"), "Ambiguous result should list candidates");

console.log("   ✓ Dynamic Resolution verified: accurately resolves unqualified and dot-notation tokens to base Mathlib definitions.\n");

// 6. Receiver type inference for dot notation
console.log("6. Testing receiver type inference (binder_context)...");
loadScript('content/binder_context.js');
const bc = context.VersoBinderContext;
assert(bc, "VersoBinderContext should be defined");

const prLines = [
  "theorem _root_.List.toFinset_sort [DecidableEq α] {l : List α} (hl : l.Nodup) :",
  "  rw [← h]",
  "  exact pairwise_sort _ r",
  "",
  "theorem _root_.List.SortedLT.sort_toFinset [LinearOrder α] {l : List α} (hl : l.SortedLT) :",
  "    l.toFinset.sort (· ≤ ·) = l :=",
  "  (List.toFinset_sort _ hl.nodup).2 hl.sortedLE.pairwise"
];
const prCtx = bc.declarationContext(prLines, prLines.length - 1);
assert(!prCtx.includes("l.Nodup"), "Context must stop at the enclosing declaration");
assert.strictEqual(bc.findBinderType("hl", prCtx), "l.SortedLT");
assert.strictEqual(bc.findBinderType("l", prCtx), "List α");
assert.strictEqual(bc.inferReceiverNamespace("hl", prCtx), "List.SortedLT", "hl.nodup → List.SortedLT.nodup");
assert.strictEqual(bc.inferReceiverNamespace("l", prCtx), "List", "l.toFinset → List.toFinset");

const cases = [
  ["theorem foo (hab : a ≤ b) : a < c :=", "hab", "LE.le"],
  ["theorem foo {s : Set α} (hs : s.Nonempty) :", "hs", "Set.Nonempty"],
  ["theorem foo (hf : Continuous f) (hg : Differentiable ℝ g) :", "hg", "Differentiable"],
  ["theorem foo (h₁ h₂ : Nat.Prime p) :", "h₂", "Nat.Prime"],
  ["theorem foo (h : ∀ x, p x) :", "h", null],
  ["theorem foo (h : P ∧ Q) :", "h", "And"],
  ["theorem foo (n : ℕ) :", "n", "Nat"],
  ["example : True := by\n  have hx : x ∈ s := by simp\n  exact hx.out", "hx", "Membership.mem"],
  ["theorem foo (h : a = b) : True := by\n  have h : Continuous f := sorry\n  exact h.comp", "h", "Continuous"],
  ["theorem foo (x : α) :", "y", null],
  // Bundled-map notations (mathlib4#45917: `g.compLinearMap`)
  ["def compLinearMap (g : (Π i, M₂ i) →ₘₛₗ[σ₂₃] N₃) (f : Π i, M₁ i →ₛₗ[σ₁₂] M₂ i) :", "g", "MultilinearMap"],
  ["def compLinearMap (g : (Π i, M₂ i) →ₘₛₗ[σ₂₃] N₃) (f : Π i, M₁ i →ₛₗ[σ₁₂] M₂ i) :", "f", null],
  ["theorem foo (m : Π i, M₁ i) :", "m", null],
  ["theorem foo (f : M →ₗ[R] N) :", "f", "LinearMap"],
  ["theorem foo (e : M ≃ₗ[R] N) :", "e", "LinearEquiv"],
  ["theorem foo (f : R →+* S) :", "f", "RingHom"],
  ["theorem foo (f : G →* H) :", "f", "MonoidHom"],
  ["theorem foo (e : α ≃ β) :", "e", "Equiv"],
  ["theorem foo (f : α ↪o β) :", "f", "OrderEmbedding"],
  ["theorem foo (f : E →L[𝕜] F) :", "f", "ContinuousLinearMap"],
  ["theorem foo (f : L →ₗ⁅R⁆ L') :", "f", "LieHom"],
  ["theorem foo (f : C(X, Y)) :", "f", "ContinuousMap"],
  ["theorem foo (f : α → β) :", "f", null],
  ["theorem foo (f : M →ₗ[R] N → P) :", "f", "LinearMap"],
  ["theorem foo (f : M →ₓ[R] N) :", "f", null],
  ["theorem foo (h : a ↔ b) :", "h", "Iff"],
  ["theorem compLinearMap_injective (f : Π i, M₁ i →ₛₗ[σ₁₂] M₂ i) (hf : ∀ i, Surjective (f i)) :\n    Injective fun g : (Π i, M₂ i) →ₘₛₗ[σ₂₃] N₃ => g.compLinearMap f", "g", "MultilinearMap"],
  ["theorem foo : ∀ x y : ℕ, x.succ = y", "y", "Nat"],
  ["theorem foo (x : ℤ) : ∃ x : ℕ, x.succ = 0", "x", "Nat"]
];
for (const [text, name, expected] of cases) {
  const got = bc.inferReceiverNamespace(name, text);
  assert.strictEqual(got, expected, `${name} in ${JSON.stringify(text)}: expected ${expected}, got ${got}`);
}

// A partial namespace matching several declarations is ambiguous, not a guess.
const monoHits = [{ name: "Set.Nonempty.mono" }, { name: "Finset.Nonempty.mono" }];
const mono = selectLoogleHit(monoHits, "Nonempty.mono", "mono");
assert(mono && !mono.hit && mono.candidates.length === 2, `Expected ambiguous Nonempty.mono, got ${JSON.stringify(mono)}`);
assert.strictEqual(selectLoogleHit(monoHits, "Set.Nonempty.mono", "mono").hit.name, "Set.Nonempty.mono");

// The service-worker selector resolves the typed token exactly.
const nodupHits = [{ name: "List.Sublist.nodup" }, { name: "List.Perm.nodup" }, { name: "List.SortedLT.nodup" }];
assert.strictEqual(selectLoogleHit(nodupHits, "List.SortedLT.nodup", "nodup").hit.name, "List.SortedLT.nodup");

console.log("   ✓ Receiver inference verified: hl.nodup with (hl : l.SortedLT) resolves in List.SortedLT.\n");

// 7. File scope (namespace / section / open) for bare identifiers
console.log("7. Testing file-scope resolution (scopeAt)...");
const scopeAt = context.scopeAt;
assert(typeof scopeAt === "function", "scopeAt should be defined by service_worker.js");
const leanFile = [
  "import Mathlib.Foo",                       // 1
  "/-! # Doc",                                // 2
  "open Nope -/",                             // 3  (inside block comment)
  "open Fin Function Finset Set",             // 4
  "section Meta",                             // 5
  "open Lean Meta",                           // 6
  "end Meta",                                 // 7
  "namespace MultilinearMap",                 // 8
  "-- open Commented",                        // 9
  "section",                                  // 10
  "open Finset (sum prod)",                   // 11
  "open scoped BigOperators",                 // 12
  "theorem cons_add (m : ∀ i : Fin n, M i.succ) :", // 13
  "    f (cons (x + y) m) = 0 := by",         // 14
  "end",                                      // 15
  "open Real in",                             // 16
  "theorem _root_.List.foo_bar : True := by", // 17
  "  exact trivial",                          // 18
  "theorem Nested.baz : True := trivial",     // 19
  "end MultilinearMap",                       // 20
  "theorem top : True := trivial"             // 21
].join("\n");
const ns = (line) => JSON.parse(JSON.stringify(scopeAt(leanFile, line).map(o => o.only ? `${o.ns}(${o.only.join(" ")})` : o.ns)));
assert.deepStrictEqual(ns(14), ["MultilinearMap", "Finset(sum prod)", "Fin", "Function", "Finset", "Set"]);
assert.deepStrictEqual(ns(18), ["List", "MultilinearMap", "Real", "Fin", "Function", "Finset", "Set"]);
assert.deepStrictEqual(ns(19), ["MultilinearMap.Nested", "MultilinearMap", "Fin", "Function", "Finset", "Set"]);
assert.deepStrictEqual(ns(21), ["Fin", "Function", "Finset", "Set"]);
assert(!ns(14).includes("Nope") && !ns(14).includes("Commented") && !ns(14).includes("Lean") && !ns(14).includes("BigOperators"),
  "Comments, closed sections and `open scoped` must not contribute names");
console.log("   ✓ File scope verified: namespaces, sections, opens, `open … in`, and declaration namespaces.\n");

// 8. Local variable tooltips and `variable` declarations (mathlib4#45909)
console.log("8. Testing local variables and PR scanning in the newer diff view...");
const declText = [
  "private theorem le_mul_exp_of_forall_abs_lt {b c e C : ℝ} (hb : 0 < b)",
  "    (h : ∀ s : ℝ, |s| < b → C ≤ c * Real.exp (e * s)) : C ≤ c * Real.exp (e * b) := by",
  "  have htend : Filter.Tendsto (fun s : ℝ => c * Real.exp (e * s))",
  "      (nhdsWithin b (Set.Iio b)) (nhds (c * Real.exp (e * b))) :=",
  "    (ContinuousAt.tendsto (h := by fun_prop)).mono_left nhdsWithin_le_nhds",
  "  filter_upwards [self_mem_nhdsWithin] with s hs1 hs2",
  "  obtain ⟨H, hH⟩ : ∃ H : ℂ → ℂ, ∀ z : ℂ, H z = 0 := sorry",
  "  rcases le_total (0 : ℝ) s with h' | h'",
  "  set y := b + 1 with hy",
  "  intro z hz"
].join("\n");
const lv = (n) => { const r = bc.localVariableInfo(n, declText); return r && r.typeSignature; };
assert.strictEqual(lv("hb"), "hb : 0 < b");
assert.strictEqual(lv("C"), "C : ℝ");
assert.strictEqual(lv("h"), "h : ∀ s : ℝ, |s| < b → C ≤ c * Real.exp (e * s)");
assert.strictEqual(lv("htend"), "htend : Filter.Tendsto (fun s : ℝ => c * Real.exp (e * s)) (nhdsWithin b (Set.Iio b)) (nhds (c * Real.exp (e * b)))");
assert.strictEqual(lv("hs2"), "hs2 : _");
assert.strictEqual(lv("H"), "H : ℂ → ℂ");
assert.strictEqual(lv("hH"), "hH : _");
assert.strictEqual(lv("h'"), "h' : _");
assert.strictEqual(lv("y"), "y := b + 1");
assert.strictEqual(lv("hz"), "hz : _");
assert.strictEqual(lv("Real"), null, "constants are not locals");
assert.strictEqual(lv("Filter.Tendsto"), null, "dotted names are not locals");

const varFile = [
  "open Complex Real",
  "variable {T : ℝ} [hT : Fact (0 < T)]",
  "public section",
  "variable {f : AddCircle T → ℂ}",
  "  (g : ℂ → ℂ)",
  "theorem foo : True := trivial",
  "end",
  "theorem bar : True := trivial"
].join("\n");
const vars = (line) => JSON.parse(JSON.stringify(context.variablesAt(varFile, line).map(v => v.line)));
assert.deepStrictEqual(vars(6), [2, 4], "both variable commands in scope inside the section");
assert.deepStrictEqual(vars(8), [2], "`end` closes `public section`'s variables");
assert.strictEqual(bc.findBinderType("g", context.variablesAt(varFile, 6)[1].text), "ℂ → ℂ", "indented continuation lines belong to `variable`");

// PR scanner: newer view, cells only, deleted lines skipped, multi-line signatures.
const cell = (text, opts = {}) => ({
  textContent: text,
  classList: { contains: () => false },
  getAttribute: (a) => (a === 'data-code-marker' ? (opts.deleted ? '-' : null) : null),
  closest: (sel) => (sel === '[data-line-number]' && opts.line ? { getAttribute: () => String(opts.line) } : null)
});
const reactRows = [
  cell("/-- A value dominated by `c * exp (e * s)` ... -/", { line: 60 }),
  cell("private theorem le_mul_exp_of_forall_abs_lt {b c e C : ℝ} (hb : 0 < b)", { line: 62 }),
  cell("    (h : ∀ s : ℝ, |s| < b → C ≤ c * Real.exp (e * s)) : C ≤ c * Real.exp (e * b) := by", { line: 63 }),
  cell("theorem old_name_deleted : True := trivial", { deleted: true }),
  cell("theorem norm_fourierCoeff_le_of_shift {f : AddCircle T → ℂ} {g : ℂ → ℂ} {M a : ℝ}", { line: 136 }),
  cell("    (hg : True) :", { line: 137 }),
  cell("    ‖fourierCoeff f k‖ ≤ M := by", { line: 138 })
];
prScanner.reset();
prScanner.scanDiffLines({ querySelectorAll: (sel) => (sel === '.diff-text-inner' ? reactRows : []) }, "Mathlib/Analysis/Fourier/StripDecay.lean");
const lm = prScanner.find("le_mul_exp_of_forall_abs_lt");
assert(lm && lm.lineNumber === 62, `le_mul_exp_of_forall_abs_lt should be indexed at line 62, got ${lm && lm.lineNumber}`);
assert(lm.typeSignature.includes("C ≤ c * Real.exp (e * b)"), `Signature should span lines: ${lm.typeSignature}`);
const nf = prScanner.find("norm_fourierCoeff_le_of_shift");
assert(nf && nf.typeSignature.endsWith("‖fourierCoeff f k‖ ≤ M"), `Multi-line signature: ${nf && nf.typeSignature}`);
assert(!prScanner.find("old_name_deleted"), "Deleted lines must not be indexed");

console.log("   ✓ Local variables, `variable` scope, and newer-view PR scanning verified.\n");

// 9. Tactic docs and tactic position
console.log("9. Testing tactic docs parsing and tactic position...");
const sampleTactics =
  '<div id="Mathlib.Meta.FunProp.funPropTacStx"><div id="userName-fun_prop"><h2>fun_prop</h2>' +
  '<p><p><code>fun_prop</code> solves a goal of the form <code>P f</code> &amp; more.</p>' +
  '<ul><li><code>fun_prop (disch := tac)</code> uses <code>tac</code>.</li></ul>' +
  '<pre><code class="language-lean">example : <a href="x">Continuous</a> (fun x : ℝ ↦ x) := by fun_prop\n</code></pre></p>' +
  '<dl><dt>Tags:</dt><dd></dd><dt>Defined in module:</dt><dd><a href="./M.html">Mathlib.Tactic.FunProp.Elab</a></dd></dl></div></div>' +
  '<div id="Other.fun_prop2"><div id="userName-fun_prop"><h2>fun_prop</h2><p>duplicate</p><dl></dl></div></div>' +
  '<div id="convSeq"><div id="userName-conv => _"><h2>conv =&gt; _</h2><p>not an identifier</p><dl></dl></div></div>';
const tdocs = context.parseTacticDocs(sampleTactics);
assert.deepStrictEqual(JSON.parse(JSON.stringify(Object.keys(tdocs))), ["fun_prop"], "one entry per identifier-like tactic name");
assert.strictEqual(tdocs.fun_prop.module, "Mathlib.Tactic.FunProp.Elab");
assert(tdocs.fun_prop.doc.startsWith("`fun_prop` solves a goal of the form `P f` & more."), tdocs.fun_prop.doc);
assert(tdocs.fun_prop.doc.includes("- `fun_prop (disch := tac)` uses `tac`."), "list items become Markdown bullets");
assert(tdocs.fun_prop.doc.includes("```lean\nexample : Continuous (fun x : ℝ ↦ x) := by fun_prop\n```"), "code blocks keep text, drop links");

const tp = (prefix) => tokenizer.isTacticPosition(prefix);
assert(tp("    "), "start of an indented line");
assert(tp("+    "), "start of an added diff line");
assert(tp("  have h := by "), "after `by`");
assert(tp("  · "), "after a focusing dot");
assert(tp("  constructor <;> "), "after `<;>`");
assert(tp("  try ("), "inside a combinator");
assert(tp("  (ContinuousAt.tendsto (h := by "), "nested `by`");
assert(!tp("  exact "), "argument position");
assert(!tp("  rw ["), "inside a rewrite list");
assert(!tp("  simpa using "), "after `using`");
assert(!tp("    have h2 : |"), "absolute-value bars are not tactic separators");
assert(tp("  first | "), "`first | tac`");
assert(tp("  first | simp | "), "later `first` alternatives");
console.log("   ✓ Tactic docs parsing and tactic-position detection verified.\n");

// 10. Receivers that are terms: `(f a).field`, `h.f₁.f₂.field`
console.log("10. Testing term receivers (conclusionOf / parenReceiver)...");
const concl = (t) => bc.conclusionOf(t);
assert.strictEqual(concl(" {X : Type u_1} [TopologicalSpace X] {f : X → Y} {x : X} (h : ContinuousAt f x) : Filter.Tendsto f (nhds x) (nhds (f x))"),
  "Filter.Tendsto f (nhds x) (nhds (f x))");
assert.strictEqual(concl("∀ s : ℝ, |s| < b → C ≤ c * Real.exp (e * s)"), "C ≤ c * Real.exp (e * s)");
assert.strictEqual(concl(" {l : List α} (h : l.SortedLT) : l.SortedLE"), "l.SortedLE");
assert.strictEqual(concl("(f : M →ₗ[R] N) : M →ₗ[R] N"), "M →ₗ[R] N", "bundled arrows are not premises");
assert.strictEqual(bc.typeHead(concl(" {l : List α} (h : l.SortedLT) : l.SortedLE"),
  (v) => bc.typeHead(bc.findBinderType(v, " {l : List α} (h : l.SortedLT) : l.SortedLE"), null)), "List.SortedLE");

assert.strictEqual(bc.parenReceiver("    (ContinuousAt.tendsto (h := by fun_prop))."), "ContinuousAt.tendsto (h := by fun_prop)");
assert.strictEqual(bc.parenReceiver("  exact (foo\n    (bar x))."), "foo\n    (bar x)", "receivers may span lines");
assert.strictEqual(bc.parenReceiver("  exact foo."), null);
assert.strictEqual(bc.applicationHead("ContinuousAt.tendsto (h := by fun_prop)"), "ContinuousAt.tendsto");
assert.strictEqual(bc.applicationHead("@hf.comp _ hg"), "hf.comp");
assert.strictEqual(bc.typeHead(bc.conclusionOf(bc.findBinderType("h", declText)), null), "LE.le", "(h s hs).le uses h's conclusion");
console.log("   ✓ Term receivers verified.\n");

// 11. Anonymous projections `h.1`, `h.2`
console.log("11. Testing anonymous projections...");
const proj = (t, n) => { const r = bc.projectionType(t, n); return r && r.type; };
assert.strictEqual(proj("0 ≤ y ∧ y ≤ s", 1), "0 ≤ y");
assert.strictEqual(proj("A ∧ B ∧ C", 2), "B ∧ C", "∧ is right-associative");
assert.strictEqual(proj("a ≤ b ↔ c ≤ d", 2), "c ≤ d → a ≤ b");
assert.strictEqual(proj("∃ H : ℂ → ℂ, ∀ z, H z = 0", 1), "ℂ → ℂ");
assert.strictEqual(proj("∃ H : ℂ → ℂ, ∀ z, H z = 0", 2), "∀ z, H z = 0");
assert.strictEqual(proj("α × (β × γ)", 2), "β × γ");
assert.strictEqual(proj("{x : ℝ // 0 < x}", 2), "0 < x");
assert.strictEqual(proj("y ∈ Set.uIcc (0 : ℝ) s", 1), "(0 : ℝ) ⊓ s ≤ y");
assert.strictEqual(proj("x ∈ Icc a b", 2), "x ≤ b");
assert.strictEqual(proj("x ∈ s ∩ t", 2), "x ∈ t");
assert.strictEqual(proj("Continuous f", 1), null, "unknown shapes defer to the structure lookup");

const uIccDecl = [
  "private theorem abs_le_abs_of_mem_uIcc' {s y : ℝ} (hy : y ∈ Set.uIcc (0 : ℝ) s) :",
  "    |y| ≤ |s| := by",
  "  rcases le_total (0 : ℝ) s with h | h",
  "  · rw [Set.uIcc_of_le h] at hy",
  "    rw [abs_of_nonneg h]",
  "    exact (abs_le).mpr ⟨by linarith [hy.1], hy.2⟩"
].join("\n");
// `hy` is rewritten before use: the projection is resolved by replaying the rewrite (section 14).
const p1 = bc.projectionInfo("hy.1", uIccDecl);
assert.strictEqual(p1.typeSignature, "hy.1 : _", "provisional until the rewrite is replayed");
assert(p1.replay && p1.docstring.includes("rw [Set.uIcc_of_le h] at hy"), "names the rewrite it applies");
assert(bc.localVariableInfo("hy", uIccDecl).replay, "hovering hy itself also replays the rewrite");
assert.strictEqual(bc.projectionInfo("hz.1", uIccDecl), null, "unknown bases are not projections");
assert.strictEqual(bc.projectionInfo("hy.le", uIccDecl), null, "named fields are not anonymous projections");
const needs = bc.projectionInfo("e.1", "theorem foo (e : α ≃ β) : True := by\n  exact e.1");
assert(needs.structureNeeded && needs.structureNeeded.index === 1, "structures ask the worker for `mk` fields");
assert.deepStrictEqual(JSON.parse(JSON.stringify(bc.laterChanges("h", "(h : P)\n  simp at h ⊢\n  norm_num at *\n  exact h", 0))),
  ["simp at h ⊢", "norm_num at *"]);
console.log("   ✓ Anonymous projections verified.\n");

// 12. Regressions from sweeping real PRs (hover every identifier)
console.log("12. Testing regressions found by sweeping real PRs...");
const tok = (line, word, nth = 0) => {
  let at = -1;
  for (let k = 0; k <= nth; k++) at = line.indexOf(word, at + 1);
  return tokenizer.extractTokenFromLine(line, at);
};
assert.strictEqual(tok("  · rw [Set.uIcc_of_le h] at hy", "uIcc_of_le").token, "Set.uIcc_of_le", "short namespaces are not stripped");
assert.strictEqual(tok("  exact hl.nodup", "nodup").token, "nodup", "lowercase receivers are stripped");
assert.strictEqual(tok("theorem _root_.List.SortedLT.foo :", "SortedLT").chainUpToCursor, "List.SortedLT", "`_root_.` is dropped");
assert.strictEqual(tok("theorem _root_.List.SortedLT.foo :", "_root_"), null);
assert.strictEqual(tok("  simpa [hx] using hy.smul x⁻¹", "x⁻¹").token, "x", "superscripts are notation");
assert.strictEqual(tok("  refine foo ?_", "?_"), null, "holes are not names");
assert.strictEqual(tok("  := fast_instance% FunLike", "fast_instance"), null, "elaborators are not names");
const arrowTok = tok("def f : R →ₙ* R →o R where", "ₙ");
assert(arrowTok.arrowNotation && arrowTok.token === "→ₙ*", `arrow notation is read whole: ${arrowTok.token}`);
assert.strictEqual(tok("def f : R →ₚ[S] R where", "ₚ").token, "→ₚ[_]");
assert.strictEqual(bc.typeHead("A →ₙ* B", null), "MulHom");
assert.strictEqual(bc.typeHead("R →ₚ[S] R", null), "PositiveLinearMap");

// Binders
assert.strictEqual(bc.findBinderType("z", "(hg : DifferentiableOn ℂ g {z : ℂ | |z.im| < a})"), "ℂ", "set-builder binder type ends at ` | `");
assert.strictEqual(bc.localVariableInfo("v", "def map (f : X) : Y where\n  carrier := f '' { v | ∀ i, v i ∈ p i }").typeSignature, "v : _");
const ascr = "theorem map_nonempty (f : X) (p : Π i, Submodule R (M i)) :\n    (map f p : Set N).Nonempty := by\n  exact (p i).zero_mem";
assert.strictEqual(bc.findBinderType("p", ascr), "Π i, Submodule R (M i)", "type ascriptions in the statement are not binders");
assert.strictEqual(bc.localVariableInfo("h₁", "theorem coe_mk (f : X → N) (h₁ h₂) : True := by\n  exact h₁").typeSignature, "h₁ : _", "untyped header binders");
assert.strictEqual(bc.findBinderType("h", "def cantorRec (o : Ordinal) : C o :=\n  if h : o = 0 then h ▸ zero else foo"), "o = 0", "`if h : P then`");
assert.strictEqual(bc.findBinderType("ha", "  · intro a\n    by_cases ha : a ∈ f.support\n    exact ha"), "a ∈ f.support", "`by_cases h : P`");
assert.strictEqual(bc.findBinderType("IH'", "  have IH' (e') : f e' < b := by\n    exact IH'"), "∀ (e'), f e' < b", "`have h (x) : T`");
assert.strictEqual(bc.localVariableInfo("o", "theorem foo : True := by\n  ext o a\n  exact o").typeSignature, "o : _", "`ext` binders");
assert.strictEqual(bc.findBinderType("h₁", "structure M where\n  (h₁ : ∀ (m : Π i, M i) (i : ι),"), "∀ (m : Π i, M i) (i : ι),", "binders spanning lines");

// Types
assert.strictEqual(bc.typeHead("Injective fun g : (Π i, M₂ i) →ₘₛₗ[σ₂₃] N₃ => g.compLinearMap f", null), "Injective", "operators inside a lambda don't count");
assert.strictEqual(bc.typeHead("Differentiable 𝕜 fun x => Complex.exp (f x)", null), "Differentiable", "`=>` is not `>`");
assert.strictEqual(bc.typeHead("((cantorNF b o).map Prod.fst).SortedGT", null), "SortedGT", "`(term).Field` gives a partial namespace");
assert.strictEqual(bc.codomainOf("Rˣ →* R ≃o R"), "R ≃o R");
assert.strictEqual(bc.structureBeingBuilt("def map (f : X) (p : Y) : SubMulAction R M where\n  carrier := f '' s"), "SubMulAction");
assert.strictEqual(bc.namedArgFunction("  have hb := le_mul_exp_of_forall_abs_lt (b := a) (c := M) ("), "le_mul_exp_of_forall_abs_lt");
assert.strictEqual(bc.namedArgFunction("  have hb := norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := T)\n      ("), "norm_integral_le_of_norm_le_const");

// PR declarations: qualified suffixes never fall back to a sibling's short name.
prScanner.reset();
prScanner.scanDiffLines({ querySelectorAll: (sel) => (sel === '.diff-text-inner' ? [
  cell("theorem _root_.List.SortedLT.sort_toFinset [LinearOrder α] {l : List α} (hl : l.SortedLT) : True := by", { line: 99 }),
  cell("theorem _root_.List.SortedGT.sort_toFinset [LinearOrder α] {l : List α} (hl : l.SortedGT) : True := by", { line: 103 }),
  cell("alias CNF.eval := cantorEval", { line: 350 })
] : []) }, "Mathlib/Data/Finset/Sort.lean");
assert.strictEqual(prScanner.find("SortedGT.sort_toFinset").lineNumber, 103);
assert.strictEqual(prScanner.find("sortedGT.sort_toFinset").lineNumber, 103, "qualifiers compare case-insensitively");
assert.strictEqual(prScanner.find("SortedEQ.sort_toFinset"), null);
assert.strictEqual(prScanner.find("CNF.eval").kind, "alias", "`alias` declarations are indexed");

// Scope origins: the current namespace is marked so it can win over `open`ed ones.
const orig = JSON.parse(JSON.stringify(context.scopeAt("namespace Finset\nopen Multiset Nat\ntheorem _root_.List.foo : True := by\n  exact pairwise_sort _ r", 4)));
assert.deepStrictEqual(orig.map(o => `${o.ns}:${o.origin}`), ["List:namespace", "Finset:namespace", "Multiset:open", "Nat:open"]);
console.log("   ✓ Sweep regressions verified.\n");

// 13. Inferring types of locals without a written type
console.log("13. Testing local type inference...");
const lt = (name, text) => { const r = bc.localVariableInfo(name, text); return r && r.typeSignature; };
const hvert = [
  "theorem foo {s : ℝ} : True := by",
  "  have hvert : ∀ y ∈ Set.uIcc (0 : ℝ) s,",
  "      g ((T : ℂ) + (y : ℂ) * Complex.I) = g ((y : ℂ) * Complex.I) := by",
  "    intro y hy"
].join("\n");
assert.strictEqual(lt("y", hvert), "y : ℝ", "element type of an interval with a typed endpoint");
assert.strictEqual(lt("hy", hvert), "hy : y ∈ Set.uIcc (0 : ℝ) s");
const hsub = "theorem foo : True := by\n  have hsub : Set.uIcc (0 : ℝ) T ×ℂ Set.uIcc (0 : ℝ) s ⊆ {z : ℂ | |z.im| < a} := by\n    intro z hz";
assert.strictEqual(lt("z", hsub), "z : ℂ", "`⊆` goals: element type");
assert.strictEqual(lt("hz", hsub), "hz : z ∈ Set.uIcc (0 : ℝ) T ×ℂ Set.uIcc (0 : ℝ) s");
const hbound = "theorem foo : True := by\n  have hbound : ∀ s : ℝ, |s| < a → ‖c‖ ≤ M * Real.exp (e * s) := by\n    intro t hsb";
assert.strictEqual(lt("t", hbound), "t : ℝ");
assert.strictEqual(lt("hsb", hbound), "hsb : |t| < a", "renamed binders are substituted");
const stmt = "theorem bar (f : ℕ → ℕ) : ∀ n : ℕ, ∀ m, n ≤ m → f n ≤ f m := by\n  intro a\n  intro b hab";
assert.strictEqual(lt("a", stmt), "a : ℕ", "intro on the declaration statement");
assert.strictEqual(lt("hab", stmt), "hab : a ≤ b", "consecutive intro lines");
assert.strictEqual(lt("b", stmt), "b : _", "untyped ∀ binders stay unknown");
const termFun = "theorem baz : ∀ x : ℝ, 0 ≤ x → 0 ≤ x ^ 2 :=\n  fun x hx => by positivity";
assert.strictEqual(lt("hx", termFun), "hx : 0 ≤ x", "term-mode `fun`");
const notGoal = "theorem q : ¬ P := by\n  intro hp";
assert.strictEqual(lt("hp", notGoal), "hp : P");
const afterRw = "theorem r : ∀ x, P x := by\n  rw [foo]\n  intro x hx";
assert.strictEqual(lt("hx", afterRw), "hx : _", "goals changed by earlier tactics are not guessed");

// Destructuring local terms
const obt = [
  "theorem t (h : ∃ x : ℝ, 0 < x ∧ x < 1) (h' : A ↔ B) : True := by",
  "  obtain ⟨x, hx0, hx1⟩ := h",
  "  rcases h' with ⟨mp, mpr⟩",
  "  set y := x + 1 with hy"
].join("\n");
assert.strictEqual(lt("x", obt), "x : ℝ");
assert.strictEqual(lt("hx0", obt), "hx0 : 0 < x");
assert.strictEqual(lt("hx1", obt), "hx1 : x < 1");
assert.strictEqual(lt("mpr", obt), "mpr : B → A");
assert.strictEqual(lt("hy", obt), "hy : y = x + 1");
const alt = "theorem u (h : a < b ∨ b < a) : True := by\n  rcases h with h1 | h2\n  · exact h1\n  · exact h2";
assert.strictEqual(lt("h2", alt), "h2 : b < a");
const ev = "theorem v (hf : ∀ᶠ x in l, 0 < f x) : True := by\n  filter_upwards [hf] with y hy";
assert.strictEqual(lt("hy", ev), "hy : 0 < f y");
// Constant terms are deferred to the worker, with the bullet they're used in.
const cst = "theorem w {b : Ordinal} : True := by\n  obtain hb | hb := le_or_gt b 1\n  · simp\n  · have := hb";
const pend = bc.localVariableInfo("hb", cst).inferNeeded;
assert(pend && pend.term === "le_or_gt b 1" && pend.caseIdx === 2, JSON.stringify(pend));
// Receivers use inferred types.
assert.strictEqual(bc.inferReceiverNamespace("hx0", obt), "LT.lt");
console.log("   ✓ Local type inference verified.\n");

// 14. Replaying `rw … at h` (async: collected and awaited before the final verdict)
console.log("14. Testing rewrite replay...");
const asyncChecks = [];
const roundTrip = ["y ∈ Set.uIcc (0 : ℝ) s", "|x| < 1", "a * b * c = 1", "c * (a * b) = 1", "¬a = b", "∀ x ∈ s, f x = 0",
  "‖f x - g x‖ ≤ ε", "(f ∘ g) x = f (g x)", "x⁻¹ * x = 1", "↑n + 1 = ↑(n + 1)", "-(a - b) = b - a", "x ∈ {z : ℂ | |z.im| < a}",
  "‖fourierCoeff f k‖ ≤ M * Real.exp (-(2 * π * a / T) * |(k : ℝ)|)", "a ≤ b ∧ b ≤ c → a ≤ c"];
for (const t of roundTrip) assert.strictEqual(bc.showTerm(bc.parseTerm(t)), t, `parse/print round trip: ${t}`);
assert.strictEqual(bc.parseTerm("x +"), null, "malformed terms don't parse");

const SIGS = {
  "Set.uIcc_of_le": "{α : Type u_1} [Lattice α] {a b : α} (h : a ≤ b) : Set.uIcc a b = Set.Icc a b",
  "Set.uIcc_of_ge": "{α : Type u_1} [Lattice α] {a b : α} (h : b ≤ a) : Set.uIcc a b = Set.Icc b a",
  "mul_comm": "{G : Type u_1} [CommMagma G] (a b : G) : a * b = b * a",
  "sub_nonneg": "{α : Type u_1} [AddGroup α] [LE α] [AddRightMono α] {a b : α} : 0 ≤ a - b ↔ b ≤ a",
  "abs_of_nonneg": "{α : Type u_1} [Lattice α] [AddGroup α] {a : α} [AddLeftMono α] (h : 0 ≤ a) : |a| = a",
  "Nat.succ_eq_add_one": "(n : ℕ) : n.succ = n + 1",
  "add_zero": "{M : Type u} [AddZeroClass M] (a : M) : a + 0 = a",
  "add_comm": "{G : Type u_1} [AddCommMagma G] (a b : G) : a + b = b + a",
  "div_eq_iff": "{G₀ : Type u_3} [GroupWithZero G₀] {a b c : G₀} (hb : b ≠ 0) : a / b = c ↔ a = c * b"
};
const sigOf = async (n) => SIGS[n] || null;
const replayed = (text, name) => {
  const info = name.includes(".") ? bc.projectionInfo(name, text) : bc.localVariableInfo(name, text);
  if (!info.replay) return Promise.resolve(info.typeSignature);
  return bc.replayChanges(info.replay.baseType, info.replay.changes, text, sigOf).then(r => bc.describeReplay(info, r).typeSignature);
};
const expectReplay = (text, name, want, why) =>
  asyncChecks.push(replayed(text, name).then(got => assert.strictEqual(got, want, why)));

const uIccFull = uIccDecl + "\n  · rw [Set.uIcc_of_ge h] at hy\n    rw [abs_of_nonpos h]\n    exact (abs_le).mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩";
expectReplay(uIccDecl, "hy", "hy : y ∈ Set.Icc (0 : ℝ) s", "rw with a lemma (Lean: hy : y ∈ Set.Icc 0 s)");
expectReplay(uIccDecl, "hy.1", "hy.1 : (0 : ℝ) ≤ y", "projection after the rewrite");
expectReplay(uIccFull, "hy", "hy : y ∈ Set.Icc s (0 : ℝ)", "only the rewrite in the current `·` case applies");
expectReplay("example (a b c : ℕ) (h : a = b + c) (hb : b = 2) : a = 2 + c := by\n  rw [hb] at h\n  exact h", "h", "h : a = 2 + c", "local equation");
expectReplay("example (x y : ℝ) (h : x * y = 1) : True := by\n  rw [mul_comm] at h\n  trivial", "h", "h : y * x = 1", "first instance fixes the variables");
expectReplay("example (a b c : ℝ) (h : a * b * c = 1) : True := by\n  nth_rw 1 [mul_comm] at h\n  trivial", "h", "h : c * (a * b) = 1", "outermost instance first, parentheses where needed");
expectReplay("example (a b : ℝ) (h : a ≤ b) : True := by\n  rw [← sub_nonneg] at h\n  trivial", "h", "h : 0 ≤ b - a", "reversed iff");
expectReplay("example (x : ℝ) (h : |x| < 1) (hx : 0 ≤ x) : x < 1 := by\n  rw [abs_of_nonneg hx] at h\n  exact h", "h", "h : x < 1", "hypothesis argument fixes variables");
expectReplay("example (a : ℝ) (h : 2 * a = 4) : True := by\n  rw [show (2 : ℝ) * a = a * 2 by ring] at h\n  trivial", "h", "h : a * 2 = 4", "`show … by` rules");
expectReplay("example (n : ℕ) (h : n.succ = 5) : True := by\n  rw [Nat.succ_eq_add_one] at h\n  trivial", "h", "h : n + 1 = 5", "dot notation in the lemma");
expectReplay("example (a b : ℝ) (h : a + b = b + a + 0) : True := by\n  rw [add_zero, add_comm] at h\n  trivial", "h", "h : b + a = b + a", "several rules in order");
expectReplay("example (f : ℕ → ℕ) (hf : ∀ n, f n = n + 1) (h : f 3 = 4) : True := by\n  rw [hf 3] at h\n  trivial", "h", "h : 3 + 1 = 4", "local ∀-equation with an argument");
expectReplay("example (x : ℝ) (h : x ∈ Set.Icc (0:ℝ) 1) : True := by\n  simp only [Set.mem_Icc] at h\n  trivial", "h", "h : x ∈ Set.Icc (0:ℝ) 1  -- outdated", "simp can't be replayed: flagged, not presented as current");
expectReplay("example (x : ℝ) (h : x ∈ Set.Icc (0:ℝ) 1) : True := by\n  simp only [Set.mem_Icc] at h\n  exact h.1", "h.1", "h.1 : _  -- outdated", "projections of an outdated type are unknown");
expectReplay("example (a b : ℕ) (h : a = b) (hb : b = 2) : True := by\n  have : a = 2 := by rw [hb] at h; exact h\n  exact trivial", "h", "h : a = b", "a rewrite inside a nested `by` doesn't leak out");
expectReplay("example (p q : Prop) (hpq : p ↔ q) (hp : p ∧ True) : q := by\n  rw [hpq] at hp\n  exact hp.1", "hp", "hp : q ∧ True", "rewriting with an iff");
expectReplay("example (x : ℝ) (h : x = 1) : True := by\n  change x = 1 at h\n  trivial", "h", "h : x = 1", "`change … at h`");
expectReplay("example (a b c : ℝ) (hc : c ≠ 0) (h : a / c = b) : True := by\n  rw [div_eq_iff hc] at h\n  trivial", "h", "h : a = b * c",
  "the lemma's own variables can't capture locals with the same names (Lean: a = b * c)");
assert.deepStrictEqual(JSON.parse(JSON.stringify(bc.hypothesisChanges("hy", "(hy : P)\n  rw [a] at hy hz ⊢\n  -- rw [b] at hy\n  norm_num at *\n  exact hy", 0).map(c => c.kind))),
  ["rw", "opaque"], "comments are ignored; `at *` counts");

Promise.all(asyncChecks).then(() => {
  console.log("   ✓ Rewrite replay verified.\n");
  console.log("==================================================");
  console.log("  ALL TESTS PASSED SUCCESSFULLY (100% OK)");
  console.log("==================================================");
}, (err) => {
  console.error(err);
  process.exit(1);
});
