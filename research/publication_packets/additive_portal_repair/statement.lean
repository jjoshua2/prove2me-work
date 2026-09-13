import Mathlib
import Definitions.Def_Hirsch_additive_portal_repair
open scoped BigOperators
open HirschRegionRoute HirschAdditiveAllowance
theorem Hirsch.additive_portal_repair_polynomial_route {V : Type*} {R : V → V → Prop} {b C h e cost : ℕ} {x y : V}
    (cert : HirschAdditiveAllowance.AdditiveRepair R b C x y h e cost) :
    HirschRegionRoute.Route R cost x y ∧ cost ≤ C*e+(1+b*C)*h*(e-b) := by sorry
