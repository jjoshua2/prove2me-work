import Solutions.PolynomialCommonFaceSmallExcessDiameter
import Solutions.PolynomialCommonFaceEffectiveRows
import Solutions.PolynomialCommonFaceMinimalSubpresentation
import Solutions.PolynomialCircuitDefectPublicBridge

/-!
# Excess-two common carriers for arbitrary feasible checkpoints

The first theorem removes the vertex-endpoint requirement from the previous
`M_min` adapter: an explicit common-face coordinate subpresentation with at
most `h+2` rows already forces intrinsic carrier diameter at most two.

The second theorem shows that parent row excess at most two automatically
supplies such a subpresentation for every source checkpoint `u` in the parent.
No circuit or checkpoint vertex hypothesis is used.
-/

open scoped RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- Any common carrier with an equivalent coordinate presentation using at most
`h+2` rows has intrinsic graph diameter at most two. Endpoints may be
nonvertices; indeed no endpoint feasibility hypothesis is needed for this
set-level statement. -/
theorem commonFace_diamLE_two_of_subpresentation_at_most
    {d n : ℕ}
    (hsmall : SmallExcessHpolyBound)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hsub : HirschCommonFace.HasSubpresentationAtMost
      (commonFaceA a b u v) (commonFaceB a b u v)
      (commonFaceDim a b u v + 2)) :
    DiamLE (commonFace a b u v) 2 := by
  obtain ⟨m, hm, e, he⟩ := hsub
  have hbdCoord := commonFace_coord_bounded a b u v hbd
  have hbdSub : Bornology.IsBounded
      (Hpoly (fun j => commonFaceA a b u v (e j))
        (fun j => commonFaceB a b u v (e j))) := by
    rw [he]
    exact hbdCoord
  have hrows : m ≤ commonFaceDim a b u v + 3 := by omega
  have hDsub : DiamLE
      (Hpoly (fun j => commonFaceA a b u v (e j))
        (fun j => commonFaceB a b u v (e j)))
      (m - commonFaceDim a b u v) :=
    hsmall (commonFaceDim a b u v) m
      (fun j => commonFaceA a b u v (e j))
      (fun j => commonFaceB a b u v (e j)) hrows hbdSub
  have hcost : m - commonFaceDim a b u v ≤ 2 := by omega
  have hDsub2 : DiamLE
      (Hpoly (fun j => commonFaceA a b u v (e j))
        (fun j => commonFaceB a b u v (e j))) 2 := by
    intro x hx y hy
    obtain ⟨w, hw0, hwB, hs⟩ := hDsub x hx y hy
    exact HirschProduct.pad_walk _ hcost w hw0 hwB hs
  have hDcoord :
      DiamLE (Hpoly (commonFaceA a b u v) (commonFaceB a b u v)) 2 := by
    rw [← he]
    exact hDsub2
  have himage := Hirsch.affineMap_diamLE_image_of_injective
    (commonFaceAffineMap a b u v)
    (commonFaceAffineMap_injective a b u v)
    (Hpoly (commonFaceA a b u v) (commonFaceB a b u v)) 2 hDcoord
  rw [commonFaceAffineMap_image_coord a b u v] at himage
  exact himage

/-- If the ambient H-presentation has row excess at most two, then every
common-face coordinate system based at a feasible point admits an equivalent
subpresentation with at most `commonFaceDim+2` rows. Rows restricting to zero
on the common direction are removed exactly, not merely ignored in a count. -/
theorem commonFace_has_subpresentation_dim_add_two_of_rows_le_dim_add_two
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b)
    (hrows : n ≤ d + 2) :
    HirschCommonFace.HasSubpresentationAtMost
      (commonFaceA a b u v) (commonFaceB a b u v)
      (commonFaceDim a b u v + 2) := by
  classical
  let A := commonFaceA a b u v
  let B := commonFaceB a b u v
  let eid : Fin n ↪ Fin n := ⟨fun i => i, by intro i j h; exact h⟩
  let F : Finset (Fin n) :=
    (Finset.univ.map eid) ∩ Finset.univ.filter (fun i => A i ≠ 0)
  have hzero :
      (0 : EuclideanSpace ℝ (Fin (commonFaceDim a b u v))) ∈ Hpoly A B := by
    apply (mem_commonFace_coord_iff a b u v 0).2
    have huF := commonFace_u_mem a b u v hu
    simpa [A, B, commonFacePoint] using huF
  obtain ⟨eF, heF⟩ := effective_subpresentation_preserves_hpoly A B hzero eid
  have hEff :=
    commonDirection_effectiveRows_card_add_dim_le_rows_add_faceDim a b u v
  have hbridge := effectiveRowsOn_commonDirection_eq_coordinateEffectiveRows a b u v
  have hcoordCount :
      (Finset.univ.filter (fun i => A i ≠ 0)).card + d ≤
        n + commonFaceDim a b u v := by
    rw [← hbridge]
    simpa [A] using hEff
  have hFle : F.card ≤ commonFaceDim a b u v + 2 := by
    have hFcard : F.card = (Finset.univ.filter (fun i => A i ≠ 0)).card := by
      simp [F, eid]
    rw [hFcard]
    omega
  refine ⟨F.card, hFle, eF, ?_⟩
  simpa [F, eid, A, B] using heF

/-- Consequently every common carrier based at a feasible checkpoint in a
bounded parent with at most two row excess has intrinsic graph diameter two. -/
theorem commonFace_diamLE_two_of_rows_le_dim_add_two
    {d n : ℕ}
    (hsmall : SmallExcessHpolyBound)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ Hpoly a b)
    (hrows : n ≤ d + 2) :
    DiamLE (commonFace a b u v) 2 := by
  exact commonFace_diamLE_two_of_subpresentation_at_most hsmall a b u v hbd
    (commonFace_has_subpresentation_dim_add_two_of_rows_le_dim_add_two
      a b u v hu hrows)

#print axioms commonFace_diamLE_two_of_subpresentation_at_most
#print axioms commonFace_has_subpresentation_dim_add_two_of_rows_le_dim_add_two
#print axioms commonFace_diamLE_two_of_rows_le_dim_add_two

end HirschCircuitLocalization
