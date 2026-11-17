import Mathlib.Topology.Basic

/-! # Module doc
namespace Fake -/

open Set Filter

namespace TopologicalSpace

variable {X : Type*} [TopologicalSpace X]
  {s t : Set X}

section Open

variable (hs : IsOpen s)
include hs

/-- doc -/
@[simp]
theorem isOpen_foo : IsOpen s := hs

theorem isOpen_foo' : IsOpen (s ∩ s) := by
  simpa using hs

end Open

open Topology in
theorem isClosed_bar (h : IsClosed s) : IsClosed s := h

omit [TopologicalSpace X] in
lemma card_eq (x : X) : x = x := rfl

def f : ℕ → ℕ
| 0 => 1
| n + 1 => f n

end TopologicalSpace

theorem _root_.foo_bar : True := trivial
