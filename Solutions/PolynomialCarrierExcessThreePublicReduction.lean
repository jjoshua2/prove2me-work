import Mathlib
import Solutions.PolynomialCarrierExcessThreeRouting

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- Public-friendly sequence reduction: an explicit `h+3` equivalent
subpresentation for each consecutive common carrier suffices for a `3L`
ordinary parent edge/stay route.  This avoids exposing the solution-local
minimum-row-count implementation in the theorem interface. -/
theorem feasible_sequence_edge_route_three_mul_of_carrier_subpresentation_at_most
    (hsmall : SmallExcessHpolyBound)
    {d n L : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hfeas : ∀ k ≤ L, w k ∈ Hpoly a b)
    (h0 : w 0 ∈ extremePoints ℝ (Hpoly a b))
    (hL : w L ∈ extremePoints ℝ (Hpoly a b))
    (hsub : ∀ i : Fin L,
      HirschCommonFace.CommonFaceHasSubpresentationAtMost a b
        (w i.val) (w (i.val + 1))
        (commonFaceDim a b (w i.val) (w (i.val + 1)) + 3)) :
    HirschRegionRoute.Route (Adj (Hpoly a b)) (3 * L) (w 0) (w L) := by
  have hP : IsCompact (Hpoly a b) :=
    Metric.isCompact_iff_isClosed_bounded.2 ⟨hpoly_isClosed a b, hbd⟩
  let B : Fin L → ℕ := fun _ => 3
  have hB : ∀ i : Fin L,
      DiamLE (commonFace a b (w i.val) (w (i.val + 1))) (B i) := by
    intro i
    simpa [B, HirschCommonFace.CommonFaceHasSubpresentationAtMost] using
      commonFace_diamLE_three_of_subpresentation_at_most hsmall a b
        (w i.val) (w (i.val + 1)) hbd (hsub i)
  have hroute := route_of_feasible_commonFace_carrier_budgets
    a b hP w L hfeas h0 hL B hB
  simpa [B, Nat.mul_comm] using hroute

#print axioms feasible_sequence_edge_route_three_mul_of_carrier_subpresentation_at_most

end HirschCircuitLocalization
