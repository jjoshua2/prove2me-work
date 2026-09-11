import Mathlib
import Definitions.Def_Hirsch_circuit_model
import Solutions.PolynomialCarrierSmallExcessBudgetRouting
import Solutions.PolynomialCircuitCheckpointMinSubpresentationDefectBounded

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- Presentation excess of the minimum equivalent common-carrier coordinate
H-presentation. -/
noncomputable def commonFacePresentationExcess {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) : ℕ :=
  commonFaceMinSubpresentationCount a b u v - commonFaceDim a b u v

/-- In a bounded parent with feasible source checkpoint, the minimum witness
itself is an `h + excess` subpresentation. -/
theorem commonFace_has_subpresentation_faceDim_add_minExcess
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ Hpoly a b) :
    HirschCommonFace.CommonFaceHasSubpresentationAtMost a b u v
      (commonFaceDim a b u v + commonFacePresentationExcess a b u v) := by
  let M := commonFaceMinSubpresentationCount a b u v
  let h := commonFaceDim a b u v
  have hdim : h ≤ M := by
    simpa [h, M] using
      commonFaceDim_le_minSubpresentation_of_bounded_feasible a b u v hbd hu
  have hspec := commonFaceMinSubpresentation_spec a b u v
  change HirschCommonFace.HasSubpresentationAtMost
    (commonFaceA a b u v) (commonFaceB a b u v) M at hspec
  obtain ⟨m, hm, e, he⟩ := hspec
  refine ⟨m, ?_, e, he⟩
  have hM : M ≤ h + (M - h) := by omega
  simpa [h, M, commonFacePresentationExcess] using hm.trans hM

/-- Exact easy-carrier cost in the natural minimum-presentation resource. If
`e = M_min-h ≤ 3`, then intrinsic common-carrier graph diameter is at most
exactly `e`. -/
theorem commonFace_diamLE_minPresentationExcess_of_le_three
    (hsmall : SmallExcessHpolyBound)
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ Hpoly a b)
    (he : commonFacePresentationExcess a b u v ≤ 3) :
    DiamLE (commonFace a b u v) (commonFacePresentationExcess a b u v) := by
  exact commonFace_diamLE_of_subpresentation_excess_le_three hsmall a b u v hbd
    (commonFacePresentationExcess a b u v) he
    (by
      simpa [HirschCommonFace.CommonFaceHasSubpresentationAtMost] using
        commonFace_has_subpresentation_faceDim_add_minExcess a b u v hbd hu)

/-- Exact additive whole-sequence routing by the intrinsic minimum-presentation
excesses.  If every step carrier has `e_i≤3`, the parent graph route costs
`sum_i e_i`, with no rounding to `3L`. -/
theorem feasible_sequence_edge_route_sum_minPresentationExcess_of_each_le_three
    (hsmall : SmallExcessHpolyBound)
    {d n L : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hfeas : ∀ k ≤ L, w k ∈ Hpoly a b)
    (h0 : w 0 ∈ extremePoints ℝ (Hpoly a b))
    (hL : w L ∈ extremePoints ℝ (Hpoly a b))
    (heasy : ∀ i : Fin L,
      commonFacePresentationExcess a b (w i.val) (w (i.val + 1)) ≤ 3) :
    HirschRegionRoute.Route (Adj (Hpoly a b))
      (∑ i : Fin L, commonFacePresentationExcess a b (w i.val) (w (i.val + 1)))
      (w 0) (w L) := by
  let R : Fin L → ℕ := fun i =>
    commonFacePresentationExcess a b (w i.val) (w (i.val + 1))
  have hsub : ∀ i : Fin L,
      HirschCommonFace.CommonFaceHasSubpresentationAtMost a b
        (w i.val) (w (i.val + 1))
        (commonFaceDim a b (w i.val) (w (i.val + 1)) + R i) := by
    intro i
    exact commonFace_has_subpresentation_faceDim_add_minExcess a b
      (w i.val) (w (i.val + 1)) hbd
      (hfeas i.val (Nat.le_of_lt i.isLt))
  have hroute := feasible_sequence_edge_route_of_carrier_excess_budgets_le_three
    hsmall a b hbd w hfeas h0 hL R (fun i => heasy i) hsub
  simpa [R] using hroute

/-- Row-circuit-walk specialization of the exact minimum-carrier-excess route.
The intermediate circuit checkpoints may be nonvertices. -/
theorem rowCircuitWalk_edge_route_sum_minPresentationExcess_of_each_le_three
    (hsmall : SmallExcessHpolyBound)
    {d n L : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hcw : RowCircuitWalk a b L u v)
    (heasy : ∀ i : Fin L,
      let w := Classical.choose hcw
      commonFacePresentationExcess a b (w i.val) (w (i.val + 1)) ≤ 3) :
    let w := Classical.choose hcw
    HirschRegionRoute.Route (Adj (Hpoly a b))
      (∑ i : Fin L, commonFacePresentationExcess a b (w i.val) (w (i.val + 1)))
      u v := by
  let w := Classical.choose hcw
  have hw := Classical.choose_spec hcw
  rcases hw with ⟨hw0, hwL, hfeas, _hsteps⟩
  have h0 : w 0 ∈ extremePoints ℝ (Hpoly a b) := by simpa [hw0] using hu
  have hL : w L ∈ extremePoints ℝ (Hpoly a b) := by simpa [hwL] using hv
  have hroute := feasible_sequence_edge_route_sum_minPresentationExcess_of_each_le_three
    hsmall a b hbd w hfeas h0 hL (by
      intro i
      simpa [w] using heasy i)
  simpa [w, hw0, hwL] using hroute

#print axioms commonFace_has_subpresentation_faceDim_add_minExcess
#print axioms commonFace_diamLE_minPresentationExcess_of_le_three
#print axioms feasible_sequence_edge_route_sum_minPresentationExcess_of_each_le_three
#print axioms rowCircuitWalk_edge_route_sum_minPresentationExcess_of_each_le_three

end HirschCircuitLocalization
