import Mathlib
import Solutions.PolynomialLowerExcessCarrierRecursion
import Solutions.PolynomialCommonFaceInjectivePresentations
import Solutions.PolynomialInjectiveCarrierParentRouting

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- Uniform graph-diameter hypothesis for all nonempty finite H-polyhedra with
injective row-evaluation map and row excess strictly below `R`.

Unlike `LowerExcessHpolyDiameterBound`, no boundedness assumption is made.  This
is the recursion interface naturally inherited by pointed one-row deletion
outers. -/
def LowerExcessInjectiveHpolyDiameterBound (R B : ℕ) : Prop :=
  ∀ (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
    (Hpoly a b).Nonempty →
    Function.Injective (HirschCircuit.rowMap a) →
    n - d < R → DiamLE (Hpoly a b) B

/-- In an injective finite H-presentation, a common carrier whose minimum
original-row presentation has strictly smaller row excess is a genuine pointed
lower-excess recursive subproblem.

The selected minimum presentation inherits row-map injectivity from the ambient
presentation, so the pointed lower-excess induction hypothesis applies without
any boundedness assumption. -/
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
  have hinjSub : Function.Injective
      (HirschCircuit.rowMap
        (fun j => commonFaceA a b u v (e j))) :=
    commonFace_subpresentation_rowMap_injective_of_injective
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

/-- Sequence-level pointed analogue of the bounded lower-excess adapter.

If every consecutive common carrier in a feasible checkpoint sequence has
minimum presentation excess strictly below `R`, then a uniform pointed
lower-excess diameter bound `B` gives an ambient parent edge/stay route of
length `B * L`.  Parent-vertex portals are supplied by the injective common-face
portal theorem, so no compactness assumption is required. -/
theorem feasible_sequence_edge_route_mul_of_carrier_minPresentationExcess_lt_of_injective
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
    HirschRegionRoute.Route (Adj (Hpoly a b)) (B * L) (w 0) (w L) := by
  let C : Fin L → ℕ := fun _ => B
  have hcarrier : ∀ i : Fin L,
      DiamLE (commonFace a b (w i.val) (w (i.val + 1))) (C i) := by
    intro i
    simpa [C] using
      commonFace_diamLE_of_minPresentationExcess_lt_of_injective
        hIH a b (w i.val) (w (i.val + 1)) hinj
        (hfeas i.val (by omega)) (hex i)
  have hlocal : ∀ i : Fin L,
      ∀ u ∈ extremePoints ℝ (Hpoly a b) ∩
          commonFace a b (w i.val) (w (i.val + 1)),
      ∀ v ∈ extremePoints ℝ (Hpoly a b) ∩
          commonFace a b (w i.val) (w (i.val + 1)),
        HirschRegionRoute.Route (Adj (Hpoly a b)) (C i) u v := by
    intro i u hu v hv
    have huFace : u ∈ extremePoints ℝ
        (commonFace a b (w i.val) (w (i.val + 1))) := by
      refine ⟨hu.2, ?_⟩
      intro p hp q hq hseg
      exact hu.1.2 hp.1 hq.1 hseg
    have hvFace : v ∈ extremePoints ℝ
        (commonFace a b (w i.val) (w (i.val + 1))) := by
      refine ⟨hv.2, ?_⟩
      intro p hp q hq hseg
      exact hv.1.2 hp.1 hq.1 hseg
    obtain ⟨q, hq0, hqC, hstep⟩ := hcarrier i u huFace v hvFace
    refine ⟨q, hq0, hqC, ?_⟩
    intro j hj
    rcases hstep j hj with heq | hadj
    · exact Or.inl heq
    · exact Or.inr (commonFace_adj_to_parent a b
        (w i.val) (w (i.val + 1)) hadj)
  have hroute :=
    HirschPointed.route_of_feasible_commonFace_parent_routes_of_rowMap_injective
      a b hinj w hfeas h0 hL C hlocal
  simpa [C, Nat.mul_comm] using hroute

#print axioms LowerExcessInjectiveHpolyDiameterBound
#print axioms commonFace_diamLE_of_minPresentationExcess_lt_of_injective
#print axioms feasible_sequence_edge_route_mul_of_carrier_minPresentationExcess_lt_of_injective

end HirschCircuitLocalization
