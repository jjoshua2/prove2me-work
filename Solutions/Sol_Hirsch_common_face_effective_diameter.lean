import Definitions.Def_Hirsch_common_face_geometry
import Solutions.PolynomialFaceEffectiveRows

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

/-- If the common-face coordinate model has at most twice its dimension many
nonzero restricted rows, any uniform diameter theorem for exactly balanced
presentations applies to that common face after deleting zero rows and padding
with tautologies. -/
theorem solution
    {d n B : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b)
    (heff : HirschCommonFace.commonFaceEffectiveCount a b u x ≤
      2 * HirschCommonFace.commonFaceDim a b u x)
    (hbalanced : ∀
      (a' : Fin (2 * HirschCommonFace.commonFaceDim a b u x) →
        EuclideanSpace ℝ (Fin (HirschCommonFace.commonFaceDim a b u x)))
      (b' : Fin (2 * HirschCommonFace.commonFaceDim a b u x) → ℝ),
      (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
      DiamLE (Hpoly a' b') B)
    (hne : (Hpoly (HirschCommonFace.commonFaceA a b u x)
      (HirschCommonFace.commonFaceB a b u x)).Nonempty)
    (hbd : Bornology.IsBounded
      (Hpoly (HirschCommonFace.commonFaceA a b u x)
        (HirschCommonFace.commonFaceB a b u x))) :
    DiamLE
      (Hpoly (HirschCommonFace.commonFaceA a b u x)
        (HirschCommonFace.commonFaceB a b u x)) B := by
  exact HirschPolynomialAccess.commonFace_coord_diam_of_balanced_effective
    a b u x hu heff hbalanced hne hbd

#print axioms solution
