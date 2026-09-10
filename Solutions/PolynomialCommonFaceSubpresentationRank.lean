import Mathlib
import Definitions.Def_Hirsch_common_face_geometry
import Solutions.PolynomialCircuitSubpresentationDefect

open scoped RealInnerProductSpace InnerProduct Convex
open Set Module Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCircuitLocalization

open HirschPolynomialAccess

variable {d n : ℕ}

/-- The zero vector in common-face coordinates represents the source vertex.
If the source is an extreme point of the ambient H-polyhedron, zero is an
extreme point of the coordinate model of the common face. -/
theorem commonFace_coord_zero_extreme
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b)) :
    (0 : EuclideanSpace ℝ (Fin (commonFaceDim a b u v))) ∈
      extremePoints ℝ
        (Hpoly (commonFaceA a b u v) (commonFaceB a b u v)) := by
  refine ⟨?_, ?_⟩
  · apply (mem_commonFace_coord_iff a b u v 0).2
    have huF := commonFace_u_mem a b u v hu.1
    simpa [commonFacePoint] using huF
  · intro p hp q hq hseg
    have hpP : commonFacePoint a b u v p ∈ Hpoly a b :=
      ((mem_commonFace_coord_iff a b u v p).1 hp).1
    have hqP : commonFacePoint a b u v q ∈ Hpoly a b :=
      ((mem_commonFace_coord_iff a b u v q).1 hq).1
    obtain ⟨α, β, hα, hβ, hαβ, hcomb⟩ := hseg
    have huSeg :
        u ∈ openSegment ℝ
          (commonFacePoint a b u v p)
          (commonFacePoint a b u v q) := by
      refine ⟨α, β, hα, hβ, hαβ, ?_⟩
      calc
        α • commonFacePoint a b u v p +
            β • commonFacePoint a b u v q =
          (α + β) • u +
            commonFaceLift a b u v (α • p + β • q) := by
              simp [commonFacePoint, map_add, map_smul]
              module
        _ = u := by rw [hαβ, hcomb]; simp
    have hpU : commonFacePoint a b u v p = u :=
      hu.2 hpP hqP huSeg
    apply commonFacePoint_injective a b u v
    simpa [commonFacePoint] using hpU

/-- Any equivalent common-face subpresentation of a face containing an ambient
vertex must retain at least `commonFaceDim` rows whose coordinate normals are
nonzero. Zero restricted rows cannot help support the coordinate vertex. -/
theorem commonFace_subpresentation_effectiveRows_card_ge_dim
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (m : ℕ) (e : Fin m ↪ Fin n)
    (he :
      Hpoly
          (fun j => HirschCommonFace.commonFaceA a b u v (e j))
          (fun j => HirschCommonFace.commonFaceB a b u v (e j)) =
        Hpoly
          (HirschCommonFace.commonFaceA a b u v)
          (HirschCommonFace.commonFaceB a b u v)) :
    HirschCommonFace.commonFaceDim a b u v ≤
      ((Finset.univ.map e) ∩
        HirschCommonFace.commonFaceEffectiveRows a b u v).card := by
  classical
  let h := HirschCommonFace.commonFaceDim a b u v
  let A := HirschCommonFace.commonFaceA a b u v
  let B := HirschCommonFace.commonFaceB a b u v
  let F : Finset (Fin n) :=
    (Finset.univ.map e) ∩ HirschCommonFace.commonFaceEffectiveRows a b u v
  let T := HirschCommonFace.rowEvalMap A F
  have h0full :
      (0 : EuclideanSpace ℝ (Fin h)) ∈
        extremePoints ℝ (Hpoly A B) := by
    simpa [h, A, B, HirschCommonFace.commonFaceDim,
      HirschPolynomialAccess.commonFaceDim,
      HirschCommonFace.commonDirection, HirschCommonFace.commonSourceRows,
      HirschCommonFace.rowEvalMap] using
      commonFace_coord_zero_extreme a b u v hu
  have h0sub :
      (0 : EuclideanSpace ℝ (Fin h)) ∈
        extremePoints ℝ
          (Hpoly (fun j => A (e j)) (fun j => B (e j))) := by
    simpa [A, B, h] using (he ▸ h0full)
  have hTin : Function.Injective T := by
    intro p q hpq
    have hz : T (p - q) = 0 := by
      rw [map_sub, hpq, sub_self]
    have hz0 := HirschPolynomialAccess.vertex_tight_rows_span_checked
      h m (fun j => A (e j)) (fun j => B (e j)) 0 h0sub (p - q) ?_
    · exact sub_eq_zero.mp hz0
    · intro j _htight
      by_cases hA : A (e j) = 0
      · simp [hA]
      have hiImage : e j ∈ Finset.univ.map e := by simp
      have hiEff : e j ∈ HirschCommonFace.commonFaceEffectiveRows a b u v := by
        simp [HirschCommonFace.commonFaceEffectiveRows, A, hA]
      have hiF : e j ∈ F := Finset.mem_inter.2 ⟨hiImage, hiEff⟩
      have hcoord := congrFun hz ⟨e j, hiF⟩
      change ⟪A (e j), p - q⟫ = 0 at hcoord
      exact hcoord
  have hle := LinearMap.finrank_le_finrank_of_injective hTin
  have hdom : Module.finrank ℝ (EuclideanSpace ℝ (Fin h)) = h :=
    finrank_euclideanSpace_fin (𝕜 := ℝ)
  have hcod : Module.finrank ℝ (F → ℝ) = F.card := by
    simp [Fintype.card_coe]
  rw [hdom, hcod] at hle
  simpa [h, F] using hle

#print axioms commonFace_coord_zero_extreme
#print axioms commonFace_subpresentation_effectiveRows_card_ge_dim

end HirschCircuitLocalization
