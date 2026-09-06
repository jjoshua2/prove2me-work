import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert

open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch

/-- Quotient-graph incidence for the $Q_{28}$ polar sign-orbits.

Four common original active inequalities force a quotient edge; a potential
gap greater than one forbids four common actives; every quotient edge changes
the stored potential by at most one; and stored tightness bits match the
integer inner product against a signed orbit representative.
-/
theorem q28_quotient_lipschitz :
    (∀ o1 o2 : Fin 20, ∀ s : Fin 16,
      4 ≤ commonActiveCard o1 o2 s → o1 = o2 ∨ QuotientAdj o1 o2) ∧
    (∀ o1 o2 : Fin 20, ∀ s : Fin 16,
      1 < max (orbitLevel o1) (orbitLevel o2) -
            min (orbitLevel o1) (orbitLevel o2) →
        commonActiveCard o1 o2 s ≤ 3) ∧
    (∀ i j : Fin 20, QuotientAdj i j → orbitLevel j ≤ orbitLevel i + 1) ∧
    (∀ o : Fin 20, ∀ s : Fin 16, ∀ i : Fin 28,
      (tightMask o s).testBit i.val = true ↔
        intDotFlip o s i = orbitDen o) := by sorry

end Hirsch
