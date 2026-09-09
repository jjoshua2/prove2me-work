import Definitions.Def_Hirsch_common_face_geometry
import Solutions.PolynomialFaceEffectiveCountBounds

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

/-- Rows common to the two defining vertices vanish after restriction to the
common-face direction space, so the number of nonzero restricted rows is at
most the total row count minus the number of common rows. -/
theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (p q : EuclideanSpace ℝ (Fin d)) :
    HirschCommonFace.commonFaceEffectiveCount a b p q ≤
      n - (HirschCommonFace.commonSourceRows a b p q).card := by
  exact HirschPolynomialAccess.commonFaceEffectiveCount_le_sub_common_card
    a b p q

#print axioms solution
