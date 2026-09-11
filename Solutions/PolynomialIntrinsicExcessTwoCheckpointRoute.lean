import Definitions.Def_Hirsch_circuit_model
import Solutions.PolynomialCircuitCarrierRouting
import Solutions.PolynomialCommonFaceExcessTwoCarrier
import Solutions.PolynomialCommonFaceMinimalSubpresentation
import Solutions.PolynomialExcessTwoWholeWalkRouting

/-!
# Whole-walk routing from per-step intrinsic carrier excess two

Unlike the ambient-excess theorem, this file makes no global assumption
`n ≤ d+2`.  It only assumes that each consecutive checkpoint carrier admits an
equivalent coordinate presentation with at most two rows beyond its intrinsic
dimension, expressed via the presentation-independent minimum row count.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- A minimum-row bound supplies the explicit subpresentation witness required
by the arbitrary-checkpoint excess-two carrier theorem. -/
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

/-- If every consecutive carrier of a feasible length-`L` checkpoint sequence
has presentation-independent intrinsic row excess at most two, then the whole
sequence can be replaced by a parent edge/stay route of length `2L`.
Intermediate checkpoints need not be vertices.  No ambient row-excess bound is
assumed. -/
theorem feasible_sequence_edge_route_two_mul_of_intrinsic_excess_two
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
    simpa [B] using commonFace_diamLE_two_of_subpresentation_at_most
      hsmall a b (w i.val) (w (i.val + 1)) hbd hsub
  have hroute := route_of_feasible_commonFace_carrier_budgets
    a b hP w L hfeas h0 hL B hB
  simpa [B, Nat.mul_comm] using hroute

/-- Row-circuit-walk specialization.  The circuit property is used only to
obtain a feasible checkpoint sequence; the routing conclusion follows entirely
from the per-step intrinsic carrier bounds. -/
theorem rowCircuitWalk_edge_route_two_mul_of_intrinsic_excess_two
    (hsmall : SmallExcessHpolyBound)
    {d n L : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hcw : RowCircuitWalk a b L u v)
    (hmin : ∀ i : Fin L,
      commonFaceMinSubpresentationCount a b
          ((Classical.choose hcw) i.val)
          ((Classical.choose hcw) (i.val + 1)) ≤
        commonFaceDim a b
          ((Classical.choose hcw) i.val)
          ((Classical.choose hcw) (i.val + 1)) + 2) :
    HirschRegionRoute.Route (Adj (Hpoly a b)) (2 * L) u v := by
  classical
  let w := Classical.choose hcw
  have hspec := Classical.choose_spec hcw
  rcases hspec with ⟨hw0, hwL, hfeas, _hsteps⟩
  have hminw : ∀ i : Fin L,
      commonFaceMinSubpresentationCount a b (w i.val) (w (i.val + 1)) ≤
        commonFaceDim a b (w i.val) (w (i.val + 1)) + 2 := by
    intro i
    simpa [w] using hmin i
  have h0 : w 0 ∈ extremePoints ℝ (Hpoly a b) := by simpa [hw0] using hu
  have hL : w L ∈ extremePoints ℝ (Hpoly a b) := by simpa [hwL] using hv
  have hroute := feasible_sequence_edge_route_two_mul_of_intrinsic_excess_two
    hsmall a b hbd w hfeas h0 hL hminw
  simpa [hw0, hwL] using hroute

#print axioms commonFace_has_subpresentation_dim_add_two_of_minCount_le
#print axioms feasible_sequence_edge_route_two_mul_of_intrinsic_excess_two
#print axioms rowCircuitWalk_edge_route_two_mul_of_intrinsic_excess_two

end HirschCircuitLocalization
