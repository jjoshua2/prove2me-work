import Mathlib
import Definitions.Def_Hirsch_model

namespace Hirsch

theorem larman_high_dimension (d n : ℕ) (hd : 4 ≤ d)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (n * 2 ^ (d - 3)) := by sorry

end Hirsch
