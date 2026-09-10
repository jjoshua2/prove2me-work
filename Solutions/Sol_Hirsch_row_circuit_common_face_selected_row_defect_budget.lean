import Solutions.PolynomialCircuitDefectPublicBridge
import Definitions.Def_Hirsch_common_face_geometry
import Definitions.Def_Hirsch_circuit_slack_model

open scoped RealInnerProductSpace
open Set Module Hirsch

noncomputable section

/-- Public adapter for the selected-row rank-defect budget on the common face
of an ambient row circuit. -/
theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u))
    (F : Finset (Fin n))
    (hF : F ⊆ HirschCommonFace.commonFaceEffectiveRows a b u v) :
    F.card +
        ((HirschCommonFace.commonFaceDim a b u v - 1) -
          Module.finrank ℝ
            (((HirschCommonFace.rowEvalMap a
              (F ∩ Finset.univ.filter (fun i =>
                a i ≠ 0 ∧ ⟪a i, v - u⟫ = 0))).domRestrict
              (HirschCommonFace.commonDirection a b u v)).range)) +
        d ≤
      n + HirschCommonFace.commonFaceDim a b u v := by
  have hF' :
      F ⊆ HirschCircuitLocalization.effectiveRowsOnSubspace a
        (HirschPolynomialAccess.commonDirection a b u v) := by
    rw [HirschCircuitLocalization.effectiveRowsOn_commonDirection_eq_publicCommonFaceEffectiveRows]
    exact hF
  have h :=
    HirschCircuitLocalization.rowCircuit_selectedEffectiveRows_defect_budget
      a b u v hu hcirc F hF'
  simpa [HirschCircuitLocalization.circuitNeutralRows,
    HirschCommonFace.commonFaceDim, HirschCommonFace.commonDirection,
    HirschCommonFace.rowEvalMap, HirschCommonFace.commonSourceRows,
    HirschPolynomialAccess.commonFaceDim, HirschPolynomialAccess.commonDirection,
    HirschPolynomialAccess.rowEvalMap, HirschPolynomialAccess.commonSourceRows] using h

#print axioms solution
