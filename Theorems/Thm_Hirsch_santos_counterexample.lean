import Mathlib
import Definitions.Def_Hirsch_model

namespace Hirsch

theorem santos_counterexample :
    ∃ (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      (Hpoly a b).Nonempty ∧ Bornology.IsBounded (Hpoly a b) ∧
      ¬ DiamLE (Hpoly a b) (n - d) := by sorry

end Hirsch
