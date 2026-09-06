import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28

open scoped RealInnerProductSpace

namespace Hirsch

theorem q28_polar_no_length_five_walk :
    ∀ w : ℕ → EuclideanSpace ℝ (Fin 5),
      ¬ (w 0 = q28U ∧ w 5 = q28V ∧
          ∀ j < 5, w j = w (j + 1) ∨ Adj (Hpoly q28A q28B) (w j) (w (j + 1))) := by sorry

end Hirsch
