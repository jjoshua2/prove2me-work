import Mathlib
open scoped BigOperators

namespace Hirsch

theorem primal_dual_support_budget_exact
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    (a : ι → E →L[ℝ] ℝ) (b lambda alpha : ι → ℝ)
    (xstar : E) (K : ℝ)
    (halpha : ∀ i, 0 ≤ alpha i)
    (hxstar : ∀ i, a i xstar ≤ b i)
    (hforms : ∀ x : E,
      (∑ i, lambda i * a i x) = ∑ i, alpha i * a i x)
    (hcomp : ∀ i, alpha i * (b i - a i xstar) = 0) :
    ((∀ x : E, (∀ i, a i x ≤ b i) →
        K ≤ (∑ i, lambda i * b i) - ∑ i, lambda i * a i x) ↔
      K ≤ (∑ i, lambda i * b i) - ∑ i, alpha i * b i) := by
  sorry

end Hirsch
