import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert

open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch

/-- Extreme points of the $Q_{28}$ polar are the stored signed orbits.

Every Euclidean extreme point of `Hpoly q28A q28B` is a coordinatewise
sign-flip of one of the twenty stored nonnegative representatives
`orbitPoint`. The orbit label of an extreme point is unique. The apices
`q28U` and `q28V` are the unsigned representatives of orbits $1$ and $0$,
and every sign-flip of those two orbits recovers the corresponding apex.
-/
theorem q28_extreme_classification :
    (∀ x : EuclideanSpace ℝ (Fin 5),
      x ∈ extremePoints ℝ (Hpoly q28A q28B) →
        ∃ o : Fin 20, ∃ s : Fin 16, x = flipPoint s (orbitPoint o)) ∧
    (∀ x : EuclideanSpace ℝ (Fin 5), ∀ o1 o2 : Fin 20, ∀ s1 s2 : Fin 16,
      x = flipPoint s1 (orbitPoint o1) →
      x = flipPoint s2 (orbitPoint o2) → o1 = o2) ∧
    q28U = flipPoint 0 (orbitPoint 1) ∧
    q28V = flipPoint 0 (orbitPoint 0) ∧
    (∀ s : Fin 16, flipPoint s (orbitPoint 1) = q28U) ∧
    (∀ s : Fin 16, flipPoint s (orbitPoint 0) = q28V) := by sorry

end Hirsch
