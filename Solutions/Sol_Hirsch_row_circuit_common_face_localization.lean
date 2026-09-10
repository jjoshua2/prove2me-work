import Solutions.PolynomialCircuitLocalization
import Definitions.Def_Hirsch_common_face_geometry
import Definitions.Def_Hirsch_circuit_slack_model

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

/-- Public adapter for the sharp vertex-to-vertex circuit localization bound. -/
theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u)) :
    2 * HirschCommonFace.commonFaceDim a b u v + d ≤ n + 1 := by
  have h := HirschCircuitLocalization.rowCircuit_commonFaceDim_localization
    a b u v hu hv hcirc
  simpa [HirschCommonFace.commonFaceDim, HirschCommonFace.commonDirection,
    HirschCommonFace.rowEvalMap, HirschCommonFace.commonSourceRows,
    HirschPolynomialAccess.commonFaceDim, HirschPolynomialAccess.commonDirection,
    HirschPolynomialAccess.rowEvalMap, HirschPolynomialAccess.commonSourceRows] using h

#print axioms solution
