import Definitions.Def_Hirsch_common_face_geometry
import Solutions.PolynomialFaceDimTradeoff

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

/-- For separated extreme endpoints, the dimensions of the two common-direction
faces through an intermediate extreme vertex overlap only through the row
excess `n - 2*d`. At exact balance `n = 2*d`, their dimensions sum to at
most `d`. -/
theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i) :
    HirschCommonFace.commonFaceDim a b u x +
      HirschCommonFace.commonFaceDim a b v x ≤ d + (n - 2 * d) := by
  have h := HirschPolynomialAccess.commonFaceDim_add_le_dim_add_excess
    a b u v x hu hv hx hsep
  simpa [HirschCommonFace.commonFaceDim,
    HirschCommonFace.commonDirection, HirschCommonFace.rowEvalMap,
    HirschCommonFace.commonSourceRows,
    HirschPolynomialAccess.commonFaceDim,
    HirschPolynomialAccess.commonDirection, HirschPolynomialAccess.rowEvalMap,
    HirschPolynomialAccess.commonSourceRows] using h

#print axioms solution
