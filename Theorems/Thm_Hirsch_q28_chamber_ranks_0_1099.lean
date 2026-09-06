import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert

open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch

/-- Combinadic ranks $0$ through $1099$ of the $Q_{28}$ chamber certificate
are accounted for by the stored singular / infeasible / orbit tag. -/
theorem q28_chamber_ranks_0_1099 :
    ∀ r : ℕ, r < 1100 → certOkUnrank r = true := by sorry

end Hirsch
