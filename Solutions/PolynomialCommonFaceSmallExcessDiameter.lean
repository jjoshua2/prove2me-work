import Solutions.PolynomialAffineDiameterTransport
import Solutions.PolynomialCommonFaceIntrinsicRowCount
import Solutions.PolynomialCommonFaceRoutingModel
import Solutions.PolynomialProductWalk

/-!
# Small intrinsic row count gives a two-edge common-face bound

This file keeps the newly published small-excess H-polyhedron theorem as an
explicit logical premise, so the geometric adapter can be kernel-audited
without importing any local theorem stub. A public wrapper can discharge that
premise with `Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three`.
-/

open scoped RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- Exact type of the public small-excess H-polyhedron theorem needed by the
common-face adapter. -/
def SmallExcessHpolyBound : Prop :=
  ∀ (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
    n ≤ d + 3 → Bornology.IsBounded (Hpoly a b) →
    DiamLE (Hpoly a b) (n - d)

/-- The canonical common-face coordinate map packaged as an affine map. -/
noncomputable def commonFaceAffineMap {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin (commonFaceDim a b u v)) →ᵃ[ℝ]
      EuclideanSpace ℝ (Fin d) where
  toFun := commonFacePoint a b u v
  linear := (commonFaceLift a b u v).toLinearMap
  map_vadd' p w := by
    change u + commonFaceLift a b u v (w + p) =
      commonFaceLift a b u v w + (u + commonFaceLift a b u v p)
    rw [map_add]
    abel

@[simp] theorem commonFaceAffineMap_apply {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (q : EuclideanSpace ℝ (Fin (commonFaceDim a b u v))) :
    commonFaceAffineMap a b u v q = commonFacePoint a b u v q := rfl

/-- The canonical affine chart is injective. -/
theorem commonFaceAffineMap_injective {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) :
    Function.Injective (commonFaceAffineMap a b u v) := by
  intro p q hpq
  exact commonFacePoint_injective a b u v hpq

/-- The canonical coordinate H-polyhedron maps ONTO the intrinsic common face,
not merely into it. -/
theorem commonFaceAffineMap_image_coord {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) :
    commonFaceAffineMap a b u v ''
        Hpoly (commonFaceA a b u v) (commonFaceB a b u v) =
      commonFace a b u v := by
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (mem_commonFace_coord_iff a b u v q).1 hq
  · intro hy
    obtain ⟨q, hq, hqy⟩ := commonFacePoint_surjOn a b u v hy
    exact ⟨q, hq, by simpa using hqy⟩

/-- Mission-facing reduction: if the presentation-independent minimum row
count of a bounded common face is at most its intrinsic dimension plus two,
then its INTRINSIC vertex-edge graph has padded diameter at most two.

The hypothesis `hsmall` is exactly the already-public small-excess theorem; it
is left explicit here to make this adapter independently auditable. -/
theorem commonFace_diamLE_two_of_minCount_le_dim_add_two
    {d n : ℕ}
    (hsmall : SmallExcessHpolyBound)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hmin : commonFaceMinSubpresentationCount a b u v ≤
      commonFaceDim a b u v + 2) :
    DiamLE (commonFace a b u v) 2 := by
  obtain ⟨m, _hmn, e, q, he, hbdSub, hirr, hstrict,
      _h0ext, _hqext, _hpoint⟩ :=
    commonFace_edgeRefinement_ready_model a b u v hbd hu hv
  have hmeq : commonFaceMinSubpresentationCount a b u v = m :=
    commonFace_minCount_eq_irredundant_subpresentation
      a b u v e he hirr hstrict
  have hmle : m ≤ commonFaceDim a b u v + 2 := by
    rw [← hmeq]
    exact hmin
  have hDsub :
      DiamLE
        (Hpoly
          (fun j => commonFaceA a b u v (e j))
          (fun j => commonFaceB a b u v (e j)))
        (m - commonFaceDim a b u v) :=
    hsmall (commonFaceDim a b u v) m
      (fun j => commonFaceA a b u v (e j))
      (fun j => commonFaceB a b u v (e j)) (by omega) hbdSub
  have hcost : m - commonFaceDim a b u v ≤ 2 := by omega
  have hDsub2 :
      DiamLE
        (Hpoly
          (fun j => commonFaceA a b u v (e j))
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

#print axioms commonFaceAffineMap_injective
#print axioms commonFaceAffineMap_image_coord
#print axioms commonFace_diamLE_two_of_minCount_le_dim_add_two

end HirschCircuitLocalization
