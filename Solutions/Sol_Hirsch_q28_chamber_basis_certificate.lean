import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert
import Theorems.Thm_Hirsch_q28_chamber_ranks_low
import Theorems.Thm_Hirsch_q28_chamber_ranks_high

open scoped RealInnerProductSpace
open Hirsch

theorem solution :
    (∀ r : ℕ, r < 2002 → certOkUnrank r = true) ∧
    (∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        unrank5 (combRank s0 s1 s2 s3 s4) = (s0, s1, s2, s3, s4)) ∧
    (∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        combRank s0 s1 s2 s3 s4 < 2002) := by
  obtain ⟨hlow, hunrank, hranklt⟩ := q28_chamber_ranks_low
  refine ⟨?certs, hunrank, hranklt⟩
  intro r hr
  rcases Nat.lt_or_ge r 1100 with h | h
  · exact hlow r h
  · exact q28_chamber_ranks_high r h hr
