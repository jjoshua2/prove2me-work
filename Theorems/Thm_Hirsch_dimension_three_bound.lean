import Mathlib
import Definitions.Def_Hirsch_model

namespace Hirsch

theorem dimension_three_bound (d n : ℕ) (hd : d ≤ 3)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (n - d) := by sorry

end Hirsch
