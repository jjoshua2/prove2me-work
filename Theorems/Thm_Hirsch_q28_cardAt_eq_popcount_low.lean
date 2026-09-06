import Mathlib
import Definitions.Def_Hirsch_q28_cert

open Hirsch

namespace Hirsch

/-- For orbit labels $0$ through $9$, the stored common-active card
equals the $28$-bit popcount of the pairwise tight-mask AND. -/
theorem q28_cardAt_eq_popcount_low :
    ∀ (o1 o2 : Fin 20) (s : Fin 16),
      o1.val < 10 →
        commonActiveCard o1 o2 s =
          popcount28 (Nat.land (tightMask o1 0) (tightMask o2 s)) := by sorry

end Hirsch
