import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert

open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch

/-- Finite sign-orbit certificate for the $Q_{28}$ polar.

The integer tables `orbitNum`/`orbitDen`/`orbitLevel`/`quotientEdges` and the
chamber-basis checker `certOkUnrank` are the exact incidence data of the
Matschke--Santos--Weibel $Q_{28}$ polar in the nonnegative orthant, reduced
by independent sign changes of the first four coordinates. The conjuncts
record: (i) four common original actives imply a quotient edge;
(ii) a level gap greater than one forbids four common actives;
(iii) quotient edges change the potential by at most one;
(iv) stored tightness masks match the integer dot product;
(v) every combinadic chamber 5-basis is accounted for by the stored
singular / infeasible / orbit certificate;
(vi) combinadic rank is inverted by `unrank5` on strictly increasing
5-tuples from `Fin 14`.
-/
theorem q28_finite_certificate :
    (∀ o1 o2 : Fin 20, ∀ s : Fin 16,
      4 ≤ commonActiveCard o1 o2 s → o1 = o2 ∨ QuotientAdj o1 o2) ∧
    (∀ o1 o2 : Fin 20, ∀ s : Fin 16,
      1 < max (orbitLevel o1) (orbitLevel o2) -
            min (orbitLevel o1) (orbitLevel o2) →
        commonActiveCard o1 o2 s ≤ 3) ∧
    (∀ i j : Fin 20, QuotientAdj i j → orbitLevel j ≤ orbitLevel i + 1) ∧
    (∀ o : Fin 20, ∀ s : Fin 16, ∀ i : Fin 28,
      (tightMask o s).testBit i.val = true ↔
        intDotFlip o s i = orbitDen o) ∧
    (∀ r : ℕ, r < 2002 → certOkUnrank r = true) ∧
    (∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        unrank5 (combRank s0 s1 s2 s3 s4) = (s0, s1, s2, s3, s4)) ∧
    (∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        combRank s0 s1 s2 s3 s4 < 2002) := by sorry

end Hirsch
