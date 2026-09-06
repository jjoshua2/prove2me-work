import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28

open scoped RealInnerProductSpace

namespace Hirsch

/-- Neighbours of the two apices of the $Q_{28}$ polar are at combinatorial
distance at least four.

This is the polar form of Matschke--Santos--Weibel Proposition 2.3: a
transversal pair of geodesic maps in $S^{3}$ with no directed $2$-cycle in
its reduced incidence pattern has width greater than $3$. Equivalently,
in the polar $5$-spindle there is no padded walk of length $3$ from a
neighbour of $u=e_5$ to a neighbour of $v=-e_5$. Combined with the two
apex-adjacent steps this forbids a walk of length $5$ between the apices.
-/
theorem q28_polar_no_length_three_between_links :
    ∀ x y : EuclideanSpace ℝ (Fin 5),
      ¬ (Adj (Hpoly q28A q28B) q28U x ∧
          Adj (Hpoly q28A q28B) y q28V ∧
          ∃ w : ℕ → EuclideanSpace ℝ (Fin 5),
            w 0 = x ∧ w 3 = y ∧
              ∀ j < 3, w j = w (j + 1) ∨
                Adj (Hpoly q28A q28B) (w j) (w (j + 1))) := by sorry

end Hirsch
