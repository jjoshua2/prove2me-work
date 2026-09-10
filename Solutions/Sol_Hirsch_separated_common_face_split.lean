import Definitions.Def_Hirsch_common_face_geometry
import Solutions.PolynomialFaceDimTradeoff

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

/-- For separated extreme endpoints, lower-dimensional diameter control through
`R-1` lets us reach a parent vertex in `B+1` steps whose common face with the
target has dimension at most `d + (n - 2*d) - R`. -/
theorem solution
    (d n R B : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i)
    (hR0 : 1 ≤ R) (hRd : R ≤ d)
    (hconnect : ∃ D : ℕ, ∃ wg : ℕ → EuclideanSpace ℝ (Fin d),
      wg 0 = u ∧ wg D = v ∧
      ∀ j < D, wg j = wg (j + 1) ∨
        Adj (Hpoly a b) (wg j) (wg (j + 1)))
    (hlow : ∀ (e : ℕ), e ≤ R - 1 →
      ∀ (a' : Fin n → EuclideanSpace ℝ (Fin e)) (b' : Fin n → ℝ),
        (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
        DiamLE (Hpoly a' b') B) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Hpoly a b) ∧
      HirschCommonFace.commonFaceDim a b v z ≤ d + (n - 2 * d) - R ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (B + 1) = z ∧
        ∀ j < B + 1,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  have h := HirschPolynomialAccess.separated_common_face_split_core
    d n R B a b hbd u v hu hv hsep hR0 hRd hconnect hlow
  simpa [HirschCommonFace.commonFaceDim,
    HirschCommonFace.commonDirection, HirschCommonFace.rowEvalMap,
    HirschCommonFace.commonSourceRows,
    HirschPolynomialAccess.commonFaceDim,
    HirschPolynomialAccess.commonDirection, HirschPolynomialAccess.rowEvalMap,
    HirschPolynomialAccess.commonSourceRows] using h

#print axioms solution
