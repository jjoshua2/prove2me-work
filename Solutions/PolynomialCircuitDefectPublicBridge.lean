import Mathlib
import Definitions.Def_Hirsch_common_face_geometry
import Solutions.PolynomialCircuitSelectedRowDefect

open scoped RealInnerProductSpace InnerProduct
open Set Module Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCircuitLocalization

open HirschPolynomialAccess

variable {d n : ℕ}

/-- A row restricts nontrivially to the common-direction subspace exactly when
its canonical common-face coordinate normal is nonzero. -/
theorem effectiveRowsOn_commonDirection_eq_coordinateEffectiveRows
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) :
    effectiveRowsOnSubspace a (commonDirection a b u v) =
      Finset.univ.filter (fun i => commonFaceA a b u v i ≠ 0) := by
  classical
  ext i
  change
    (∃ x : commonDirection a b u v,
      ⟪a i, (x : EuclideanSpace ℝ (Fin d))⟫ ≠ 0) ↔
      commonFaceA a b u v i ≠ 0
  constructor
  · rintro ⟨x, hx⟩ hA0
    let q := commonFaceRepr a b u v x
    have hinner := commonFace_inner_restricted a b u v i q
    have hlift : commonFaceLift a b u v q =
        (x : EuclideanSpace ℝ (Fin d)) := by
      change (((commonFaceRepr a b u v).symm
        ((commonFaceRepr a b u v) x) : commonDirection a b u v) :
        EuclideanSpace ℝ (Fin d)) =
        (x : EuclideanSpace ℝ (Fin d))
      rw [(commonFaceRepr a b u v).symm_apply_apply]
    rw [hA0, inner_zero_left, hlift] at hinner
    exact hx hinner.symm
  · intro hA
    let q := commonFaceA a b u v i
    let x : commonDirection a b u v :=
      ⟨commonFaceLift a b u v q,
        commonFaceLift_mem_direction a b u v q⟩
    refine ⟨x, ?_⟩
    change ⟪a i, commonFaceLift a b u v q⟫ ≠ 0
    rw [← commonFace_inner_restricted a b u v i q]
    dsimp [q]
    exact inner_self_ne_zero.mpr hA

/-- The internal effective-row set agrees definitionally with the already
public common-face effective-row vocabulary. -/
theorem effectiveRowsOn_commonDirection_eq_publicCommonFaceEffectiveRows
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) :
    effectiveRowsOnSubspace a (commonDirection a b u v) =
      HirschCommonFace.commonFaceEffectiveRows a b u v := by
  rw [effectiveRowsOn_commonDirection_eq_coordinateEffectiveRows]
  rfl

#print axioms effectiveRowsOn_commonDirection_eq_coordinateEffectiveRows
#print axioms effectiveRowsOn_commonDirection_eq_publicCommonFaceEffectiveRows

end HirschCircuitLocalization
