import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert

open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch

/-- Adjacency on the $Q_{28}$ polar descends to the stored quotient.

An extreme segment of `Hpoly q28A q28B` joins two signed orbit
representatives whose orbit labels are equal or form an edge of
`QuotientAdj`.
-/
theorem q28_adj_to_orbit :
    ∀ x y : EuclideanSpace ℝ (Fin 5),
      Adj (Hpoly q28A q28B) x y →
        ∃ o1 o2 : Fin 20, ∃ s1 s2 : Fin 16,
          x = flipPoint s1 (orbitPoint o1) ∧
          y = flipPoint s2 (orbitPoint o2) ∧
          (o1 = o2 ∨ QuotientAdj o1 o2) := by sorry

end Hirsch
