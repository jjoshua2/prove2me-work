import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert

open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch

/-- Completeness of the combinadic chamber-basis certificate for $Q_{28}$.

Every strictly increasing $5$-tuple from the $14$ nonnegative-chamber
inequalities has combinadic rank in $\{0,\ldots,2001\}$, the stored unranking
map inverts that rank, and every such rank is accounted for by the stored
singular / infeasible / orbit tag.
-/
theorem q28_chamber_basis_certificate :
    (∀ r : ℕ, r < 2002 → certOkUnrank r = true) ∧
    (∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        unrank5 (combRank s0 s1 s2 s3 s4) = (s0, s1, s2, s3, s4)) ∧
    (∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        combRank s0 s1 s2 s3 s4 < 2002) := by sorry

end Hirsch
