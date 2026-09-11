import Mathlib
import Definitions.Def_Hirsch_common_face_geometry
import Definitions.Def_Hirsch_circuit_model
import Solutions.PolynomialCircuitDefectPublicBridge
import Solutions.PolynomialCircuitDeletionSavings

open scoped BigOperators RealInnerProductSpace InnerProduct
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Hirsch

/-- Public-vocabulary form of the exact selected-row savings identity for a
bounded nonvertex row-circuit carrier.

Let `h` be the canonical common-carrier dimension, `E` its public effective-row
set, `Z` the nonzero ambient rows neutral on the circuit displacement, and `F`
a selected subset of `E` with at least `h` rows.  If `delta` is the neutral-rank
defect of `F`, then the entire ambient row excess splits exactly as

`(F.card-h) + delta + kappa + s + tau = n-d`,

where `kappa` is surplus row disappearance, `s` counts omitted nonneutral
effective rows, and `tau` is omitted neutral-row redundancy beyond actual rank
loss.  This is one-carrier accounting, not a routing theorem. -/
theorem row_circuit_selected_excess_defect_savings_identity
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b)) (hx : x ∈ Hpoly a b)
    (hcirc : IsRowCircuit a (y - x))
    (F : Finset (Fin n))
    (hF : F ⊆ HirschCommonFace.commonFaceEffectiveRows a b x y)
    (hface : HirschCommonFace.commonFaceDim a b x y ≤ F.card) :
    let h := HirschCommonFace.commonFaceDim a b x y
    let E := HirschCommonFace.commonFaceEffectiveRows a b x y
    let Z := Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, y - x⟫ = 0)
    let delta := (h - 1) -
      Module.finrank ℝ
        (((HirschCommonFace.rowEvalMap a (F ∩ Z)).domRestrict
          (HirschCommonFace.commonDirection a b x y)).range)
    (F.card - h) + delta +
      (n + h - (E.card + d)) +
      ((E \ F) \ Z).card + (((E \ F) ∩ Z).card - delta) = n - d := by
  classical
  have hF' :
      F ⊆ HirschCircuitLocalization.effectiveRowsOnSubspace a
        (HirschPolynomialAccess.commonDirection a b x y) := by
    rw [HirschCircuitLocalization.effectiveRowsOn_commonDirection_eq_publicCommonFaceEffectiveRows]
    exact hF
  have hface' : HirschPolynomialAccess.commonFaceDim a b x y ≤ F.card := by
    simpa [HirschCommonFace.commonFaceDim, HirschCommonFace.commonDirection,
      HirschCommonFace.rowEvalMap, HirschCommonFace.commonSourceRows,
      HirschPolynomialAccess.commonFaceDim,
      HirschPolynomialAccess.commonDirection,
      HirschPolynomialAccess.rowEvalMap,
      HirschPolynomialAccess.commonSourceRows] using hface
  have h :=
    HirschCircuitLocalization.rowCircuit_selected_excess_defect_savings_identity_of_bounded
      a b x y hbd hx hcirc F hF' hface'
  rw [HirschCircuitLocalization.effectiveRowsOn_commonDirection_eq_publicCommonFaceEffectiveRows
    a b x y] at h
  simpa [HirschCircuitLocalization.circuitNeutralRows,
    HirschCommonFace.commonFaceDim, HirschCommonFace.commonDirection,
    HirschCommonFace.rowEvalMap, HirschCommonFace.commonSourceRows,
    HirschPolynomialAccess.commonFaceDim,
    HirschPolynomialAccess.commonDirection,
    HirschPolynomialAccess.rowEvalMap,
    HirschPolynomialAccess.commonSourceRows] using h

#print axioms row_circuit_selected_excess_defect_savings_identity

end Hirsch