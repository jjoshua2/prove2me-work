import Mathlib
import Definitions.Def_Hirsch_q28_cert

open Hirsch

set_option maxHeartbeats 8000000

theorem solution :
    ∀ (o1 o2 : Fin 20) (s : Fin 16),
      o1.val < 10 →
        commonActiveCard o1 o2 s =
          popcount28 (Nat.land (tightMask o1 0) (tightMask o2 s)) := by
  intro o1
  fin_cases o1 <;> decide
