import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert

open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch

/-- Low combinadic ranks of the $Q_{28}$ chamber certificate.

Every combinadic rank in $\{0,\ldots,1099\}$ is accounted for by the stored
singular / infeasible / orbit tag, combinadic rank is inverted on strictly
increasing $5$-tuples from $\{0,\ldots,13\}$, and those ranks lie in
$\{0,\ldots,2001\}$.
-/
theorem q28_chamber_ranks_low :
    (∀ r : ℕ, r < 1100 → certOkUnrank r = true) ∧
    (∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        unrank5 (combRank s0 s1 s2 s3 s4) = (s0, s1, s2, s3, s4)) ∧
    (∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        combRank s0 s1 s2 s3 s4 < 2002) := by sorry

end Hirsch
