import Mathlib
import Solutions.PolynomialCommonFaceCoords

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 3000000

noncomputable section

namespace HirschPolynomialAccess

variable {d n : ℕ}

noncomputable def commonFaceAffineMap
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin (commonFaceDim a b u x)) →ᵃ[ℝ]
      EuclideanSpace ℝ (Fin d) :=
  (commonFaceLift a b u x).toLinearMap.toAffineMap +
    AffineMap.const ℝ _ u

lemma commonFaceAffineMap_apply
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (q : EuclideanSpace ℝ (Fin (commonFaceDim a b u x))) :
    commonFaceAffineMap a b u x q = commonFacePoint a b u x q := by
  simp [commonFaceAffineMap, commonFacePoint, add_comm]

lemma commonFace_coord_extreme_of_face_extreme
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    {q : EuclideanSpace ℝ (Fin (commonFaceDim a b u x))}
    (hqF : commonFacePoint a b u x q ∈
      extremePoints ℝ (commonFace a b u x)) :
    q ∈ extremePoints ℝ
      (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)) := by
  let Q := Hpoly (commonFaceA a b u x) (commonFaceB a b u x)
  have hqQ : q ∈ Q := (mem_commonFace_coord_iff a b u x q).2 hqF.1
  refine ⟨hqQ, ?_⟩
  intro p hp r hr hopen
  have hmapopen : commonFacePoint a b u x q ∈
      openSegment ℝ (commonFacePoint a b u x p) (commonFacePoint a b u x r) := by
    rw [← commonFaceAffineMap_apply a b u x q,
      ← commonFaceAffineMap_apply a b u x p,
      ← commonFaceAffineMap_apply a b u x r,
      ← image_openSegment ℝ (commonFaceAffineMap a b u x) p r]
    exact ⟨q, hopen, rfl⟩
  have hpF : commonFacePoint a b u x p ∈ commonFace a b u x :=
    (mem_commonFace_coord_iff a b u x p).1 hp
  have hrF : commonFacePoint a b u x r ∈ commonFace a b u x :=
    (mem_commonFace_coord_iff a b u x r).1 hr
  have heq := hqF.2 hpF hrF hmapopen
  exact commonFacePoint_injective a b u x heq

lemma commonFace_face_extreme_of_coord_extreme
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    {q : EuclideanSpace ℝ (Fin (commonFaceDim a b u x))}
    (hq : q ∈ extremePoints ℝ
      (Hpoly (commonFaceA a b u x) (commonFaceB a b u x))) :
    commonFacePoint a b u x q ∈
      extremePoints ℝ (commonFace a b u x) := by
  let Q := Hpoly (commonFaceA a b u x) (commonFaceB a b u x)
  have hqF : commonFacePoint a b u x q ∈ commonFace a b u x :=
    (mem_commonFace_coord_iff a b u x q).1 hq.1
  refine ⟨hqF, ?_⟩
  intro y hy z hz hopen
  obtain ⟨p, hpQ, hpy⟩ := commonFacePoint_surjOn a b u x hy
  obtain ⟨r, hrQ, hrz⟩ := commonFacePoint_surjOn a b u x hz
  have hopen' : commonFacePoint a b u x q ∈
      openSegment ℝ (commonFacePoint a b u x p) (commonFacePoint a b u x r) := by
    simpa [hpy, hrz] using hopen
  have himage : commonFacePoint a b u x q ∈
      (commonFaceAffineMap a b u x) '' openSegment ℝ p r := by
    rw [image_openSegment]
    simpa [commonFaceAffineMap_apply] using hopen'
  obtain ⟨s, hsopen, hsq⟩ := himage
  have hsq' : commonFacePoint a b u x s = commonFacePoint a b u x q := by
    simpa [commonFaceAffineMap_apply] using hsq
  have hs : s = q := commonFacePoint_injective a b u x hsq'
  subst s
  have hpq : p = q := hq.2 hpQ hrQ hsopen
  subst p
  simpa using hpy.symm

lemma commonFace_coord_adj_to_face
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    {p q : EuclideanSpace ℝ (Fin (commonFaceDim a b u x))}
    (hadj : Adj
      (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)) p q) :
    Adj (commonFace a b u x)
      (commonFacePoint a b u x p) (commonFacePoint a b u x q) := by
  let Q := Hpoly (commonFaceA a b u x) (commonFaceB a b u x)
  have hne : commonFacePoint a b u x p ≠ commonFacePoint a b u x q := by
    intro h
    exact hadj.1 (commonFacePoint_injective a b u x h)
  refine ⟨hne, ?_⟩
  refine ⟨?_, ?_⟩
  · intro y hyseg
    have hyimg : y ∈ (commonFaceAffineMap a b u x) '' segment ℝ p q := by
      rw [image_segment]
      simpa [commonFaceAffineMap_apply] using hyseg
    obtain ⟨r, hrseg, hry⟩ := hyimg
    have hrQ : r ∈ Q := hadj.2.subset hrseg
    have hrF : commonFacePoint a b u x r ∈ commonFace a b u x :=
      (mem_commonFace_coord_iff a b u x r).1 hrQ
    have hry' : commonFacePoint a b u x r = y := by
      simpa only [commonFaceAffineMap_apply] using hry
    exact hry' ▸ hrF
  · intro y hyF z hzF w hwseg hwopen
    obtain ⟨r, hrQ, hry⟩ := commonFacePoint_surjOn a b u x hyF
    obtain ⟨s, hsQ, hsz⟩ := commonFacePoint_surjOn a b u x hzF
    have hwimg : w ∈ (commonFaceAffineMap a b u x) '' segment ℝ p q := by
      rw [image_segment]
      simpa [commonFaceAffineMap_apply] using hwseg
    obtain ⟨t, htseg, htw⟩ := hwimg
    have hopen' : commonFacePoint a b u x t ∈
        openSegment ℝ (commonFacePoint a b u x r) (commonFacePoint a b u x s) := by
      have htw' : commonFacePoint a b u x t = w := by
        simpa [commonFaceAffineMap_apply] using htw
      simpa [hry, hsz, htw'] using hwopen
    have hopenimg : commonFacePoint a b u x t ∈
        (commonFaceAffineMap a b u x) '' openSegment ℝ r s := by
      rw [image_openSegment]
      simpa [commonFaceAffineMap_apply] using hopen'
    obtain ⟨t', ht'open, ht'eq⟩ := hopenimg
    have htt' : t' = t := by
      apply commonFacePoint_injective a b u x
      simpa [commonFaceAffineMap_apply] using ht'eq
    subst t'
    have hrseg : r ∈ segment ℝ p q :=
      hadj.2.left_mem_of_mem_openSegment hrQ hsQ htseg ht'open
    have hryseg : commonFacePoint a b u x r ∈
        segment ℝ (commonFacePoint a b u x p) (commonFacePoint a b u x q) := by
      rw [← commonFaceAffineMap_apply a b u x r,
        ← commonFaceAffineMap_apply a b u x p,
        ← commonFaceAffineMap_apply a b u x q,
        ← image_segment]
      exact ⟨r, hrseg, rfl⟩
    simpa [hry] using hryseg

lemma commonFace_coord_adj_to_parent
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    {p q : EuclideanSpace ℝ (Fin (commonFaceDim a b u x))}
    (hadj : Adj
      (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)) p q) :
    Adj (Hpoly a b)
      (commonFacePoint a b u x p) (commonFacePoint a b u x q) :=
  commonFace_adj_to_parent a b u x (commonFace_coord_adj_to_face a b u x hadj)

end HirschPolynomialAccess
