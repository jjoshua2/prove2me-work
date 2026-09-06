import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert

open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch

/-- High combinadic ranks of the $Q_{28}$ chamber certificate.

Every combinadic rank in $\{1100,\ldots,2001\}$ is accounted for by the stored
singular / infeasible / orbit tag.
-/
theorem q28_chamber_ranks_high :
    ∀ r : ℕ, 1100 ≤ r → r < 2002 → certOkUnrank r = true := by sorry

end Hirsch
