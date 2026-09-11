import Mathlib
import Definitions.Def_Hirsch_common_face_geometry
import Definitions.Def_Hirsch_circuit_slack_model
import Solutions.PolynomialCircuitCheckpointMinSubpresentationDefect
import Solutions.PolynomialCircuitBoundedNeutralRank

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- Public-vocabulary nonvertex extension of the common-face
subpresentation excess/defect theorem.  The source checkpoint need only be
feasible in a bounded parent; one reference parent vertex supplies the global
neutral-rank witness. -/
theorem rowCircuit_commonFace_subpresentation_excess_defect_checkpoint
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (z x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hz : z ∈ extremePoints ℝ (Hpoly a b))
    (hx : x ∈ Hpoly a b)
    (hcirc : IsRowCircuit a (y - x))
    (M : ℕ)
    (hsub : HirschCommonFace.CommonFaceHasSubpresentationAtMost a b x y M) :
    ∃ m : ℕ, m ≤ M ∧ ∃ e : Fin m ↪ Fin n,
      Hpoly
          (fun j => HirschCommonFace.commonFaceA a b x y (e j))
          (fun j => HirschCommonFace.commonFaceB a b x y (e j)) =
        Hpoly
          (HirschCommonFace.commonFaceA a b x y)
          (HirschCommonFace.commonFaceB a b x y) ∧
      let F : Finset (Fin n) :=
        (Finset.univ.map e) ∩ HirschCommonFace.commonFaceEffectiveRows a b x y
      HirschCommonFace.commonFaceDim a b x y ≤ F.card ∧
      F.card ≤ M ∧
      (F.card - HirschCommonFace.commonFaceDim a b x y) +
          ((HirschCommonFace.commonFaceDim a b x y - 1) -
            Module.finrank ℝ
              (((HirschCommonFace.rowEvalMap a
                (F ∩ Finset.univ.filter (fun i =>
                  a i ≠ 0 ∧ ⟪a i, y - x⟫ = 0))).domRestrict
                (HirschCommonFace.commonDirection a b x y)).range)) ≤
        n - d := by
  classical
  change HirschCommonFace.HasSubpresentationAtMost
    (HirschCommonFace.commonFaceA a b x y)
    (HirschCommonFace.commonFaceB a b x y) M at hsub
  obtain ⟨m, hm, e, he⟩ := hsub
  refine ⟨m, hm, e, he, ?_⟩
  let F : Finset (Fin n) :=
    (Finset.univ.map e) ∩ HirschCommonFace.commonFaceEffectiveRows a b x y
  have hFpub : F ⊆ HirschCommonFace.commonFaceEffectiveRows a b x y :=
    Finset.inter_subset_right
  have hFint : F ⊆ effectiveRowsOnSubspace a (commonDirection a b x y) := by
    rw [effectiveRowsOn_commonDirection_eq_publicCommonFaceEffectiveRows]
    exact hFpub
  have hFM : F.card ≤ M := by
    calc
      F.card ≤ (Finset.univ.map e).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = m := by simp
      _ ≤ M := hm
  have hzero :
      (0 : EuclideanSpace ℝ (Fin (commonFaceDim a b x y))) ∈
        Hpoly (commonFaceA a b x y) (commonFaceB a b x y) := by
    apply (mem_commonFace_coord_iff a b x y 0).2
    have hxF := commonFace_u_mem a b x y hx
    simpa [commonFacePoint] using hxF
  obtain ⟨eF, heF⟩ := effective_subpresentation_preserves_hpoly
    (commonFaceA a b x y) (commonFaceB a b x y) hzero e
  have hbdCoord := commonFace_coord_bounded a b x y hbd
  have hbdSel : Bornology.IsBounded
      (Hpoly (fun j => commonFaceA a b x y (e j))
        (fun j => commonFaceB a b x y (e j))) := by
    rw [he]
    exact hbdCoord
  have hzeroSel :
      (0 : EuclideanSpace ℝ (Fin (commonFaceDim a b x y))) ∈
        Hpoly (fun j => commonFaceA a b x y (e j))
          (fun j => commonFaceB a b x y (e j)) := by
    rw [he]
    exact hzero
  have hbdF : Bornology.IsBounded
      (Hpoly (fun j => commonFaceA a b x y (eF j))
        (fun j => commonFaceB a b x y (eF j))) := by
    rw [heF]
    exact hbdSel
  have hzeroF :
      (0 : EuclideanSpace ℝ (Fin (commonFaceDim a b x y))) ∈
        Hpoly (fun j => commonFaceA a b x y (eF j))
          (fun j => commonFaceB a b x y (eF j)) := by
    rw [heF]
    exact hzeroSel
  have hinj := HirschCircuit.rowMap_injective_of_bounded
    (fun j => commonFaceA a b x y (eF j))
    (fun j => commonFaceB a b x y (eF j)) hbdF 0 hzeroF
  have hdimRank := LinearMap.finrank_le_finrank_of_injective hinj
  have hface : commonFaceDim a b x y ≤ F.card := by
    simpa [finrank_euclideanSpace_fin] using hdimRank
  have hdn : d ≤ n :=
    rows_ge_dimension_of_bounded a b hbd z (extremePoints_subset hz)
  have hbudget := rowCircuit_selectedEffectiveRows_excess_defect_of_reference_vertex
    a b z x y hz hcirc F hFint hface hdn
  refine ⟨?_, hFM, ?_⟩
  · simpa [F, HirschCommonFace.commonFaceDim, HirschCommonFace.commonDirection,
      HirschCommonFace.commonSourceRows, HirschCommonFace.rowEvalMap,
      HirschPolynomialAccess.commonFaceDim, HirschPolynomialAccess.commonDirection,
      HirschPolynomialAccess.commonSourceRows, HirschPolynomialAccess.rowEvalMap] using hface
  · simpa [F, circuitNeutralRows,
      HirschCommonFace.commonFaceDim, HirschCommonFace.commonDirection,
      HirschCommonFace.commonSourceRows, HirschCommonFace.rowEvalMap,
      HirschPolynomialAccess.commonFaceDim, HirschPolynomialAccess.commonDirection,
      HirschPolynomialAccess.commonSourceRows, HirschPolynomialAccess.rowEvalMap] using hbudget

#print axioms rowCircuit_commonFace_subpresentation_excess_defect_checkpoint

end HirschCircuitLocalization
