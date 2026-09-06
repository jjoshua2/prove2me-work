import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert

open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch

/-- Extreme points of the $Q_{28}$ polar are the $20$ stored sign-orbits,
and adjacency of extreme points descends to the signed quotient graph.

The first conjunct says every Euclidean extreme point of
`Hpoly q28A q28B` is a coordinatewise sign-flip of one of the twenty
stored nonnegative representatives `orbitPoint`. The second says that an
extreme segment joins representatives whose orbit labels are equal or
form an edge of `QuotientAdj`. The last two conjuncts identify the
apices: `q28U` (resp. `q28V`) is the unsigned representative of orbit
$1$ (resp. $0$), and sign-flips of those two orbits are the apices
themselves.
-/
theorem q28_polar_orbit_identification :
    (∀ x : EuclideanSpace ℝ (Fin 5),
      x ∈ extremePoints ℝ (Hpoly q28A q28B) →
        ∃ o : Fin 20, ∃ s : Fin 16, x = flipPoint s (orbitPoint o)) ∧
    (∀ x y : EuclideanSpace ℝ (Fin 5),
      Adj (Hpoly q28A q28B) x y →
        ∃ o1 o2 : Fin 20, ∃ s1 s2 : Fin 16,
          x = flipPoint s1 (orbitPoint o1) ∧
          y = flipPoint s2 (orbitPoint o2) ∧
          (o1 = o2 ∨ QuotientAdj o1 o2)) ∧
    (∀ x : EuclideanSpace ℝ (Fin 5), ∀ o1 o2 : Fin 20, ∀ s1 s2 : Fin 16,
      x = flipPoint s1 (orbitPoint o1) →
      x = flipPoint s2 (orbitPoint o2) → o1 = o2) ∧
    q28U = flipPoint 0 (orbitPoint 1) ∧
    q28V = flipPoint 0 (orbitPoint 0) ∧
    (∀ s : Fin 16, flipPoint s (orbitPoint 1) = q28U) ∧
    (∀ s : Fin 16, flipPoint s (orbitPoint 0) = q28V) := by sorry

end Hirsch
