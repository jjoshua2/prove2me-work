import Mathlib
import Definitions.Def_Hirsch_common_face_geometry
import Solutions.PolynomialCircuitDefectPublicBridge

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCircuitLocalization

open HirschPolynomialAccess

variable {d n : ℕ}

/-- If the common-face coordinate polyhedron has a subpresentation using at
most `M` original rows, the effective rows occurring in that actual
subpresentation form a selected set of size at most `M` and obey the circuit
rank-defect budget.

This ties the previously proved selected-row inequality to a genuine
presentation of the common face without yet identifying the minimum
subpresentation size with the geometric number of true facets. -/
theorem rowCircuit_commonFace_subpresentation_defect_budget
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u))
    (M : ℕ)
    (hsub : HirschCommonFace.CommonFaceHasSubpresentationAtMost a b u v M) :
    ∃ m : ℕ, m ≤ M ∧ ∃ e : Fin m ↪ Fin n,
      Hpoly
          (fun j => HirschCommonFace.commonFaceA a b u v (e j))
          (fun j => HirschCommonFace.commonFaceB a b u v (e j)) =
        Hpoly
          (HirschCommonFace.commonFaceA a b u v)
          (HirschCommonFace.commonFaceB a b u v) ∧
      let F : Finset (Fin n) :=
        (Finset.univ.map e) ∩ HirschCommonFace.commonFaceEffectiveRows a b u v
      F.card ≤ M ∧
        F.card +
            ((HirschCommonFace.commonFaceDim a b u v - 1) -
              Module.finrank ℝ
                (((HirschCommonFace.rowEvalMap a
                  (F ∩ Finset.univ.filter (fun i =>
                    a i ≠ 0 ∧ ⟪a i, v - u⟫ = 0))).domRestrict
                  (HirschCommonFace.commonDirection a b u v)).range)) +
            d ≤
          n + HirschCommonFace.commonFaceDim a b u v := by
  classical
  change HirschCommonFace.HasSubpresentationAtMost
    (HirschCommonFace.commonFaceA a b u v)
    (HirschCommonFace.commonFaceB a b u v) M at hsub
  obtain ⟨m, hm, e, he⟩ := hsub
  refine ⟨m, hm, e, he, ?_⟩
  let F : Finset (Fin n) :=
    (Finset.univ.map e) ∩ HirschCommonFace.commonFaceEffectiveRows a b u v
  have hFpub : F ⊆ HirschCommonFace.commonFaceEffectiveRows a b u v := by
    exact Finset.inter_subset_right
  have hFint :
      F ⊆ effectiveRowsOnSubspace a (commonDirection a b u v) := by
    rw [effectiveRowsOn_commonDirection_eq_publicCommonFaceEffectiveRows]
    exact hFpub
  have hbudget := rowCircuit_selectedEffectiveRows_defect_budget
    a b u v hu hcirc F hFint
  have hFcard : F.card ≤ M := by
    calc
      F.card ≤ (Finset.univ.map e).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = m := by simp
      _ ≤ M := hm
  dsimp only
  refine ⟨hFcard, ?_⟩
  simpa [F, circuitNeutralRows,
    HirschCommonFace.commonFaceDim, HirschCommonFace.commonDirection,
    HirschCommonFace.rowEvalMap, HirschCommonFace.commonSourceRows,
    HirschPolynomialAccess.commonFaceDim, HirschPolynomialAccess.commonDirection,
    HirschPolynomialAccess.rowEvalMap, HirschPolynomialAccess.commonSourceRows] using hbudget

#print axioms rowCircuit_commonFace_subpresentation_defect_budget

end HirschCircuitLocalization
