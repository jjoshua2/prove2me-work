import Mathlib
import Solutions.PolynomialLowerExcessCarrierRecursion
import Solutions.PolynomialCommonFaceInjectivePresentations
import Solutions.PolynomialInjectiveCarrierParentRouting
import Solutions.PolynomialCircuitInjectiveMinCarrierDichotomy
import Solutions.PolynomialCircuitCarrierThreeWayReduction

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 6000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess HirschRegionRoute

/-- Induction interface for nonempty pointed finite H-polyhedra of strictly
smaller row excess. Pointedness is supplied as row-map injectivity; boundedness
is deliberately NOT assumed. This is a hypothesis, not a global diameter claim. -/
def LowerExcessInjectiveHpolyDiameterBound (R B : ℕ) : Prop :=
  ∀ (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
    (Hpoly a b).Nonempty → Function.Injective (HirschCircuit.rowMap a) →
    n - d < R → DiamLE (Hpoly a b) B

/-- Strict minimum-carrier excess is a genuine recursive subproblem even in an
unbounded pointed parent. Equivalent minimum presentations retain injectivity,
and the affine coordinate map preserves actual graph edges and diameter.
Neither checkpoint is required to be a vertex. -/
theorem commonFace_diamLE_of_minPresentationExcess_lt_of_injective
    {R B d n : ℕ}
    (hIH : LowerExcessInjectiveHpolyDiameterBound R B)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (HirschCircuit.rowMap a))
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
  have hinjSub := commonFace_subpresentation_rowMap_injective_of_injective
    a b u v hu hinj e heqInt
  have hsub :
      DiamLE
        (Hpoly
          (fun j => commonFaceA a b u v (e j))
          (fun j => commonFaceB a b u v (e j))) B := by
    apply hIH h M
      (fun j => commonFaceA a b u v (e j))
      (fun j => commonFaceB a b u v (e j))
      ⟨0, hzeroSub⟩ hinjSub
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

/-- Weighted edge-route assembly for strict carriers in a pointed parent.
Shared nonvertex checkpoints are replaced by genuine parent-vertex portals.
Every supplied local budget is paid once per indexed carrier; no compactness or
boundedness is used. Repeated equal carriers are not asserted to be distinct. -/
theorem feasible_sequence_edge_route_sum_of_strict_carriers_of_injective
    {R d n L : ℕ}
    (C : Fin L → ℕ)
    (hIH : ∀ i, LowerExcessInjectiveHpolyDiameterBound R (C i))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hfeas : ∀ k ≤ L, w k ∈ Hpoly a b)
    (h0 : w 0 ∈ extremePoints ℝ (Hpoly a b))
    (hL : w L ∈ extremePoints ℝ (Hpoly a b))
    (hex : ∀ i : Fin L,
      commonFaceMinSubpresentationCount a b (w i.val) (w (i.val + 1)) -
        commonFaceDim a b (w i.val) (w (i.val + 1)) < R) :
    Route (Adj (Hpoly a b)) (∑ i, C i) (w 0) (w L) := by
  have hlocal : ∀ i : Fin L,
      ∀ u ∈ extremePoints ℝ (Hpoly a b) ∩
          commonFace a b (w i.val) (w (i.val + 1)),
      ∀ v ∈ extremePoints ℝ (Hpoly a b) ∩
          commonFace a b (w i.val) (w (i.val + 1)),
        Route (Adj (Hpoly a b)) (C i) u v := by
    intro i
    exact extreme_face_region (Hpoly a b)
      (commonFace a b (w i.val) (w (i.val + 1))) (C i)
      (commonFace_isExtreme a b _ _)
      (commonFace_diamLE_of_minPresentationExcess_lt_of_injective
        (hIH i) a b (w i.val) (w (i.val + 1)) hinj
        (hfeas i.val (by omega)) (hex i))
  exact HirschPointed.route_of_feasible_commonFace_parent_routes_of_rowMap_injective
    a b hinj w hfeas h0 hL C hlocal

/-- Uniform-budget specialization. In particular a certified strict-carrier
sequence of length `17*m^3` costs `B*(17*m^3)` ordinary edges/stays.
The structural strictness premise is essential; cubic circuit length alone
cannot discharge it. -/
theorem feasible_sequence_edge_route_mul_of_strict_carriers_of_injective
    {R B d n L : ℕ}
    (hIH : LowerExcessInjectiveHpolyDiameterBound R B)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hfeas : ∀ k ≤ L, w k ∈ Hpoly a b)
    (h0 : w 0 ∈ extremePoints ℝ (Hpoly a b))
    (hL : w L ∈ extremePoints ℝ (Hpoly a b))
    (hex : ∀ i : Fin L,
      commonFaceMinSubpresentationCount a b (w i.val) (w (i.val + 1)) -
        commonFaceDim a b (w i.val) (w (i.val + 1)) < R) :
    Route (Adj (Hpoly a b)) (B * L) (w 0) (w L) := by
  have hroute := feasible_sequence_edge_route_sum_of_strict_carriers_of_injective
    (fun _ : Fin L => B) (fun _ => hIH)
    a b hinj w hfeas h0 hL hex
  simpa [Nat.mul_comm] using hroute

/-- Turn the pointed same-phase strict/blocker resource split into a real local
edge-cost split. Strict resource is discharged by lower-excess pointed
induction; the remaining branch keeps the full essential trapped-blocker
certificate. No bound for that remaining branch is asserted. -/
theorem rowCircuitStep_same_phase_recursive_or_essential_trapped_blocker_of_injective
    {d n B : ℕ}
    (hIH : LowerExcessInjectiveHpolyDiameterBound (n - d) B)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y v : EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (hstep : RowCircuitStep a b x y)
    (hv : v ∈ Hpoly a b)
    (M : ℝ) (hM : 0 ≤ M) (r : Fin n → ℝ)
    (heqx : HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v) r =
      HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v)
        (HirschCircuit.slack a b x))
    (heqy : HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v) r =
      HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v)
        (HirschCircuit.slack a b y)) :
    DiamLE (commonFace a b x y) B ∨
      CommonFaceHasEssentialTrappedBlocker a b x y v M r := by
  obtain ⟨m, hm, e, heq, hirr, hstrictRows, hmin, hcase⟩ :=
    rowCircuitStep_irredundant_minPresentation_same_phase_strict_budget_or_essential_trapped_blocker_of_injective
      a b x y v hinj hstep hv M hM r heqx heqy
  dsimp only at hcase
  rcases hcase with hbudget | hblocker
  · left
    have hex : commonFaceMinSubpresentationCount a b x y -
        commonFaceDim a b x y < n - d := by
      rw [hmin]
      omega
    exact commonFace_diamLE_of_minPresentationExcess_lt_of_injective
      hIH a b x y hinj hstep.1 hex
  · right
    exact ⟨m, hm, e, heq, hirr, hstrictRows, hmin, hblocker⟩

#print axioms commonFace_diamLE_of_minPresentationExcess_lt_of_injective
#print axioms feasible_sequence_edge_route_sum_of_strict_carriers_of_injective
#print axioms feasible_sequence_edge_route_mul_of_strict_carriers_of_injective
#print axioms rowCircuitStep_same_phase_recursive_or_essential_trapped_blocker_of_injective

end HirschCircuitLocalization
