import Mathlib
import Solutions.PolynomialCircuitCarrierRouting
import Solutions.PolynomialCommonFaceExcessTwoCarrier
import Solutions.PolynomialCommonFaceMinimalSubpresentation
import Solutions.PolynomialExcessTwoWholeWalkRouting

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- Any common carrier admitting an equivalent coordinate H-presentation with
at most `h+3` rows has intrinsic graph diameter at most three.  This is an
intrinsic carrier condition; the ambient parent may have arbitrary row excess. -/
theorem commonFace_diamLE_three_of_subpresentation_at_most
    {d n : ℕ}
    (hsmall : SmallExcessHpolyBound)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hsub : HirschCommonFace.HasSubpresentationAtMost
      (commonFaceA a b u v) (commonFaceB a b u v)
      (commonFaceDim a b u v + 3)) :
    DiamLE (commonFace a b u v) 3 := by
  obtain ⟨m, hm, e, he⟩ := hsub
  have hbdCoord := commonFace_coord_bounded a b u v hbd
  have hbdSub : Bornology.IsBounded
      (Hpoly (fun j => commonFaceA a b u v (e j))
        (fun j => commonFaceB a b u v (e j))) := by
    rw [he]
    exact hbdCoord
  have hrows : m ≤ commonFaceDim a b u v + 3 := hm
  have hDsub : DiamLE
      (Hpoly (fun j => commonFaceA a b u v (e j))
        (fun j => commonFaceB a b u v (e j)))
      (m - commonFaceDim a b u v) :=
    hsmall (commonFaceDim a b u v) m
      (fun j => commonFaceA a b u v (e j))
      (fun j => commonFaceB a b u v (e j)) hrows hbdSub
  have hcost : m - commonFaceDim a b u v ≤ 3 := by omega
  have hDsub3 : DiamLE
      (Hpoly (fun j => commonFaceA a b u v (e j))
        (fun j => commonFaceB a b u v (e j))) 3 := by
    intro x hx y hy
    obtain ⟨w, hw0, hwB, hs⟩ := hDsub x hx y hy
    exact HirschProduct.pad_walk _ hcost w hw0 hwB hs
  have hDcoord :
      DiamLE (Hpoly (commonFaceA a b u v) (commonFaceB a b u v)) 3 := by
    rw [← he]
    exact hDsub3
  have himage := Hirsch.affineMap_diamLE_image_of_injective
    (commonFaceAffineMap a b u v)
    (commonFaceAffineMap_injective a b u v)
    (Hpoly (commonFaceA a b u v) (commonFaceB a b u v)) 3 hDcoord
  rw [commonFaceAffineMap_image_coord a b u v] at himage
  exact himage

/-- Presentation-independent form: if the minimum equivalent original-row
coordinate presentation has row excess at most three, the intrinsic carrier
diameter is at most three.  No checkpoint-vertex hypothesis is needed. -/
theorem commonFace_diamLE_three_of_minCount_le_dim_add_three
    {d n : ℕ}
    (hsmall : SmallExcessHpolyBound)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hmin : commonFaceMinSubpresentationCount a b u v ≤
      commonFaceDim a b u v + 3) :
    DiamLE (commonFace a b u v) 3 := by
  have hspec := commonFaceMinSubpresentation_spec a b u v
  change HirschCommonFace.HasSubpresentationAtMost
    (commonFaceA a b u v) (commonFaceB a b u v)
    (commonFaceMinSubpresentationCount a b u v) at hspec
  obtain ⟨m, hm, e, he⟩ := hspec
  apply commonFace_diamLE_three_of_subpresentation_at_most hsmall a b u v hbd
  exact ⟨m, hm.trans hmin, e, he⟩

/-- General whole-sequence reduction: if every consecutive common carrier of a
feasible checkpoint sequence has intrinsic presentation excess at most three,
then the parent vertex graph can replace the entire sequence with three ordinary
edge/stay steps per old step.  The ambient parent may have arbitrary row excess. -/
theorem feasible_sequence_edge_route_three_mul_of_carrier_minCount_le_dim_add_three
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
        commonFaceDim a b (w i.val) (w (i.val + 1)) + 3) :
    HirschRegionRoute.Route (Adj (Hpoly a b)) (3 * L) (w 0) (w L) := by
  have hP : IsCompact (Hpoly a b) :=
    Metric.isCompact_iff_isClosed_bounded.2 ⟨hpoly_isClosed a b, hbd⟩
  let B : Fin L → ℕ := fun _ => 3
  have hB : ∀ i : Fin L,
      DiamLE (commonFace a b (w i.val) (w (i.val + 1))) (B i) := by
    intro i
    simpa [B] using
      commonFace_diamLE_three_of_minCount_le_dim_add_three hsmall a b
        (w i.val) (w (i.val + 1)) hbd (hmin i)
  have hroute := route_of_feasible_commonFace_carrier_budgets
    a b hP w L hfeas h0 hL B hB
  simpa [B, Nat.mul_comm] using hroute

#print axioms commonFace_diamLE_three_of_subpresentation_at_most
#print axioms commonFace_diamLE_three_of_minCount_le_dim_add_three
#print axioms feasible_sequence_edge_route_three_mul_of_carrier_minCount_le_dim_add_three

end HirschCircuitLocalization
