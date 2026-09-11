import Mathlib
import Solutions.PolynomialCommonFaceSmallExcessDiameter
import Solutions.PolynomialCircuitCarrierRouting
import Solutions.PolynomialCircuitCheckpointMinSubpresentationDefect

open scoped RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- Uniform diameter hypothesis for all bounded nonempty finite H-polyhedra
whose row excess is strictly below `R`. This is the induction interface used to
solve a strict common-carrier subproblem without assuming any circuit structure
inside that carrier. -/
def LowerExcessHpolyDiameterBound (R B : ℕ) : Prop :=
  ∀ (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
    (Hpoly a b).Nonempty → Bornology.IsBounded (Hpoly a b) →
    n - d < R → DiamLE (Hpoly a b) B

/-- A common carrier whose minimum original-row presentation has row excess
strictly below `R` is a genuine recursive lower-excess H-polytope subproblem.
Any uniform diameter theorem for lower-excess H-polyhedra therefore transports
to the intrinsic common carrier.

No circuit, maximality, or endpoint-extremality hypothesis is needed here; only
the source checkpoint must be feasible so the carrier coordinate polytope is
nonempty. -/
theorem commonFace_diamLE_of_minPresentationExcess_lt
    {R B d n : ℕ}
    (hIH : LowerExcessHpolyDiameterBound R B)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ Hpoly a b)
    (hex : commonFaceMinSubpresentationCount a b u v -
      commonFaceDim a b u v < R) :
    DiamLE (commonFace a b u v) B := by
  classical
  let M := commonFaceMinSubpresentationCount a b u v
  let h := commonFaceDim a b u v
  obtain ⟨e, heq, _hFeq⟩ :=
    commonFace_minSubpresentation_effective_witness_of_feasible a b u v hu
  have heqInt :
      Hpoly
          (fun j => commonFaceA a b u v (e j))
          (fun j => commonFaceB a b u v (e j)) =
        Hpoly (commonFaceA a b u v) (commonFaceB a b u v) := by
    have heq' := heq
    change
      Hpoly
          (fun j => commonFaceA a b u v (e j))
          (fun j => commonFaceB a b u v (e j)) =
        Hpoly (commonFaceA a b u v) (commonFaceB a b u v) at heq'
    exact heq'
  have hzeroFull :
      (0 : EuclideanSpace ℝ (Fin h)) ∈
        Hpoly (commonFaceA a b u v) (commonFaceB a b u v) := by
    apply (mem_commonFace_coord_iff a b u v 0).2
    simpa [commonFacePoint, h] using commonFace_u_mem a b u v hu
  have hzeroSub :
      (0 : EuclideanSpace ℝ (Fin h)) ∈
        Hpoly
          (fun j => commonFaceA a b u v (e j))
          (fun j => commonFaceB a b u v (e j)) := by
    intro j
    exact hzeroFull (e j)
  have hbdCoord := commonFace_coord_bounded a b u v hbd
  have hbdSub : Bornology.IsBounded
      (Hpoly
        (fun j => commonFaceA a b u v (e j))
        (fun j => commonFaceB a b u v (e j))) := by
    rw [heqInt]
    exact hbdCoord
  have hsub :
      DiamLE
        (Hpoly
          (fun j => commonFaceA a b u v (e j))
          (fun j => commonFaceB a b u v (e j))) B := by
    apply hIH h M
      (fun j => commonFaceA a b u v (e j))
      (fun j => commonFaceB a b u v (e j))
      ⟨0, hzeroSub⟩ hbdSub
    simpa [M, h] using hex
  have hcoord :
      DiamLE (Hpoly (commonFaceA a b u v) (commonFaceB a b u v)) B := by
    rw [← heqInt]
    exact hsub
  have himage := Hirsch.affineMap_diamLE_image_of_injective
    (commonFaceAffineMap a b u v)
    (commonFaceAffineMap_injective a b u v)
    (Hpoly (commonFaceA a b u v) (commonFaceB a b u v)) B hcoord
  rw [commonFaceAffineMap_image_coord a b u v] at himage
  exact himage

/-- Sequence-level portal version of the same induction interface. If every
consecutive common carrier in a feasible checkpoint sequence has minimum row
excess strictly below `R`, then a uniform lower-excess diameter bound `B`
provides a parent edge/stay route of length `B * L`.

This is the exact adapter needed to discharge the strict branch of a
row-excess induction. -/
theorem feasible_sequence_edge_route_mul_of_carrier_minPresentationExcess_lt
    {R B d n L : ℕ}
    (hIH : LowerExcessHpolyDiameterBound R B)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hfeas : ∀ k ≤ L, w k ∈ Hpoly a b)
    (h0 : w 0 ∈ extremePoints ℝ (Hpoly a b))
    (hL : w L ∈ extremePoints ℝ (Hpoly a b))
    (hex : ∀ i : Fin L,
      commonFaceMinSubpresentationCount a b (w i.val) (w (i.val + 1)) -
        commonFaceDim a b (w i.val) (w (i.val + 1)) < R) :
    HirschRegionRoute.Route (Adj (Hpoly a b)) (B * L) (w 0) (w L) := by
  have hclosed : IsClosed (Hpoly a b) := by
    rw [show Hpoly a b = ⋂ i : Fin n,
        {x : EuclideanSpace ℝ (Fin d) | ⟪a i, x⟫ ≤ b i} by
      ext x
      simp [Hpoly]]
    exact isClosed_iInter (fun i =>
      isClosed_le (continuous_const.inner continuous_id) continuous_const)
  have hP : IsCompact (Hpoly a b) :=
    Metric.isCompact_iff_isClosed_bounded.2 ⟨hclosed, hbd⟩
  let C : Fin L → ℕ := fun _ => B
  have hC : ∀ i : Fin L,
      DiamLE (commonFace a b (w i.val) (w (i.val + 1))) (C i) := by
    intro i
    simpa [C] using
      commonFace_diamLE_of_minPresentationExcess_lt
        hIH a b (w i.val) (w (i.val + 1)) hbd
        (hfeas i.val (Nat.le_trans i.isLt.le (Nat.le_refl L))) (hex i)
  have hroute := route_of_feasible_commonFace_carrier_budgets
    a b hP w L hfeas h0 hL C hC
  simpa [C, Nat.mul_comm] using hroute

#print axioms commonFace_diamLE_of_minPresentationExcess_lt
#print axioms feasible_sequence_edge_route_mul_of_carrier_minPresentationExcess_lt

end HirschCircuitLocalization
