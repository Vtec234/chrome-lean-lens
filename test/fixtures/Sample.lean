/-- Doubles a number. -/
def double (n : Nat) : Nat := n + n

theorem double_eq (n : Nat) : double n = 2 * n := by
  unfold double
  omega

theorem add_comm' (a b : Nat) (h : a = b) : a + b = b + a := by
  have h₁ : b + a = a + b := by
    rw [Nat.add_comm]
  rw [h₁]

theorem two_cases (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · have hq' : q := by exact hq
    exact hq'

theorem ind (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Nat.add_succ, ih]

def unused (x y : Nat) : Nat := x

#check double

example : (1 : Nat) = 2 := by
  rfl

theorem wide (𝕜 : Nat) (h𝕜 : 𝕜 = 𝕜) : 𝕜 + 0 = 𝕜 := by
  simp
