import Solutions.PolynomialCircuitDefectPublicBridge
import Definitions.Def_Hirsch_common_face_geometry
import Definitions.Def_Hirsch_circuit_slack_model

open scoped RealInnerProductSpace
open Set Module Hirsch

noncomputable section

/-- Public adapter for the exact neutral-row rank of an ambient row circuit on
its common-face direction space. -/
theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u)) :
    Module.finrank ℝ
        (((HirschCommonFace.rowEvalMap a
          (Finset.univ.filter (fun i =>
            a i ≠ 0 ∧ ⟪a i, v - u⟫ = 0))).domRestrict
          (HirschCommonFace.commonDirection a b u v)).range) =
      HirschCommonFace.commonFaceDim a b u v - 1 := by
  have h :=
    HirschCircuitLocalization.rowCircuit_neutral_rank_on_commonDirection_eq_commonFaceDim_sub_one
      a b u v hu hcirc
  simpa [HirschCircuitLocalization.circuitNeutralRows,
    HirschCommonFace.commonFaceDim, HirschCommonFace.commonDirection,
    HirschCommonFace.rowEvalMap, HirschCommonFace.commonSourceRows,
    HirschPolynomialAccess.commonFaceDim, HirschPolynomialAccess.commonDirection,
    HirschPolynomialAccess.rowEvalMap, HirschPolynomialAccess.commonSourceRows] using h

#print axioms solution
