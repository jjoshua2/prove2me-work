import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

theorem balanced_polynomial_bound :
    ∃ C k : ℕ, ∀ (D : ℕ) (a : Fin (2 * D) → EuclideanSpace ℝ (Fin D)) (b : Fin (2 * D) → ℝ),
      (Hpoly a b).Nonempty → Bornology.IsBounded (Hpoly a b) →
      DiamLE (Hpoly a b) (C * D ^ k) := by sorry

end Hirsch
