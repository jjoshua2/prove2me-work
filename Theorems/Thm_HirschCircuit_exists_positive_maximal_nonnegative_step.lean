import Mathlib

set_option autoImplicit false

namespace HirschCircuit

/-- For a nonnegative point, a direction that is nonnegative on all currently
zero coordinates and negative somewhere admits a strictly positive maximal
step before nonnegativity fails. -/
theorem exists_positive_maximal_nonnegative_step {n : ℕ}
    (x g : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hzero : ∀ i, x i = 0 → 0 ≤ g i)
    (hneg : ∃ i, g i < 0) :
    ∃ α : ℝ, 0 < α ∧ (∀ i, 0 ≤ x i + α * g i) ∧
      (∃ q, g q < 0 ∧ x q + α * g q = 0) ∧
      ∀ β : ℝ, α < β → ∃ i, x i + β * g i < 0 := by sorry

end HirschCircuit
