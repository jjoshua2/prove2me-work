import Solutions.PolynomialCircuitStepProgress
import Definitions.Def_Hirsch_common_face_geometry
import Definitions.Def_Hirsch_circuit_slack_model

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

/-- Public adapter: maximality removes the destination-nullity term from
nonvertex circuit localization. -/
theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (z x y : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ extremePoints ℝ (Hpoly a b))
    (hstep : RowCircuitStep a b x y) :
    HirschCommonFace.commonFaceDim a b x y + d ≤
      n + HirschCommonFace.commonFaceDim a b x x := by
  have h := HirschCircuitLocalization.rowCircuitStep_commonFaceDim_source_bound
    a b z x y hz hstep
  simpa [HirschCommonFace.commonFaceDim, HirschCommonFace.commonDirection,
    HirschCommonFace.rowEvalMap, HirschCommonFace.commonSourceRows,
    HirschPolynomialAccess.commonFaceDim, HirschPolynomialAccess.commonDirection,
    HirschPolynomialAccess.rowEvalMap, HirschPolynomialAccess.commonSourceRows] using h

#print axioms solution
