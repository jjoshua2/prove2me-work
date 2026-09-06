import Mathlib
import Definitions.Def_Hirsch_model

namespace Hirsch

theorem polynomial_hirsch_conjecture :
    ∃ c k : ℕ, ∀ (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      (Hpoly a b).Nonempty → Bornology.IsBounded (Hpoly a b) →
      DiamLE (Hpoly a b) (c * (n + d) ^ k) := by sorry

end Hirsch
