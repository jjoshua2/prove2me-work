import Mathlib
import Definitions.Def_Hirsch_circuit_model
import Solutions.PolynomialExcessTwoWholeWalkRouting
import Solutions.PolynomialCommonFaceMinimalSubpresentation

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- If the least original-row subpresentation of a common carrier uses at most
`commonFaceDim + 2` rows, then the explicit minimum witness is also an
`h+2`-row subpresentation suitable for the arbitrary-checkpoint diameter-two
adapter. -/
theorem commonFace_has_subpresentation_dim_add_two_of_minCount_le
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hmin : commonFaceMinSubpresentationCount a b u v ≤
      commonFaceDim a b u v + 2) :
    HirschCommonFace.HasSubpresentationAtMost
      (commonFaceA a b u v) (commonFaceB a b u v)
      (commonFaceDim a b u v + 2) := by
  have hspec := commonFaceMinSubpresentation_spec a b u v
  change HirschCommonFace.HasSubpresentationAtMost
    (commonFaceA a b u v) (commonFaceB a b u v)
    (commonFaceMinSubpresentationCount a b u v) at hspec
  obtain ⟨m, hm, e, he⟩ := hspec
  exact ⟨m, hm.trans hmin, e, he⟩

/-- A feasible checkpoint sequence has a `2L` parent edge/stay refinement when
EACH SELECTED consecutive common carrier has intrinsic minimum row-presentation
excess at most two. The ambient parent may have arbitrarily many excess rows.
Interior checkpoints need not be vertices. -/
theorem feasible_sequence_edge_route_two_mul_of_minCounts
    (hsmall : SmallExcessHpolyBound)
    {d n L : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hfeas : ∀ k ≤ L, w k ∈ Hpoly a b)
    (h0 : w 0 ∈ extremePoints ℝ (Hpoly a b))
    (hL : w L ∈ extremePoints ℝ (Hpoly a b))
    (hmin : ∀ i : Fin L,
      commonFaceMinSubpresentationCount a b (w i.val) (w (i.val + 1)) ≤
        commonFaceDim a b (w i.val) (w (i.val + 1)) + 2) :
    HirschRegionRoute.Route (Adj (Hpoly a b)) (2 * L) (w 0) (w L) := by
  have hP : IsCompact (Hpoly a b) :=
    Metric.isCompact_iff_isClosed_bounded.2 ⟨hpoly_isClosed a b, hbd⟩
  let B : Fin L → ℕ := fun _ => 2
  have hB : ∀ i : Fin L,
      DiamLE (commonFace a b (w i.val) (w (i.val + 1))) (B i) := by
    intro i
    have hsub := commonFace_has_subpresentation_dim_add_two_of_minCount_le
      a b (w i.val) (w (i.val + 1)) (hmin i)
    simpa [B] using
      commonFace_diamLE_two_of_subpresentation_at_most hsmall a b
        (w i.val) (w (i.val + 1)) hbd hsub
  have hroute := route_of_feasible_commonFace_carrier_budgets
    a b hP w L hfeas h0 hL B hB
  simpa [B, Nat.mul_comm] using hroute

/-- Uniform intrinsic excess-two control on ALL feasible common carriers of the
parent turns every padded row-circuit walk of length `L` into a parent edge/stay
route of length at most `2L`. This removes the ambient `n ≤ d+2` hypothesis;
the quantitative obligation has moved to an intrinsic carrier statement. -/
theorem rowCircuitWalk_edge_route_two_mul_of_uniform_minCount
    (hsmall : SmallExcessHpolyBound)
    {d n L : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hmin : ∀ p q : EuclideanSpace ℝ (Fin d),
      p ∈ Hpoly a b → q ∈ Hpoly a b →
      commonFaceMinSubpresentationCount a b p q ≤
        commonFaceDim a b p q + 2)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hcw : RowCircuitWalk a b L u v) :
    HirschRegionRoute.Route (Adj (Hpoly a b)) (2 * L) u v := by
  obtain ⟨w, hw0, hwL, hfeas, _hsteps⟩ := hcw
  have h0 : w 0 ∈ extremePoints ℝ (Hpoly a b) := by simpa [hw0] using hu
  have hL : w L ∈ extremePoints ℝ (Hpoly a b) := by simpa [hwL] using hv
  have hlocal : ∀ i : Fin L,
      commonFaceMinSubpresentationCount a b (w i.val) (w (i.val + 1)) ≤
        commonFaceDim a b (w i.val) (w (i.val + 1)) + 2 := by
    intro i
    exact hmin (w i.val) (w (i.val + 1))
      (hfeas i.val (Nat.le_of_lt i.isLt))
      (hfeas (i.val + 1) (by omega))
  have hroute := feasible_sequence_edge_route_two_mul_of_minCounts
    hsmall a b hbd w hfeas h0 hL hlocal
  simpa [hw0, hwL] using hroute

#print axioms commonFace_has_subpresentation_dim_add_two_of_minCount_le
#print axioms feasible_sequence_edge_route_two_mul_of_minCounts
#print axioms rowCircuitWalk_edge_route_two_mul_of_uniform_minCount

end HirschCircuitLocalization
