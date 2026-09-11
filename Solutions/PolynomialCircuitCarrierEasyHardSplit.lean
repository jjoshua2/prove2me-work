import Mathlib
import Solutions.PolynomialMinCarrierExcessRouting
import Solutions.PolynomialCircuitCheckpointMinSubpresentationDefectBounded

open scoped BigOperators RealInnerProductSpace
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- A feasible row-circuit step has a sharp formal easy/hard split in the
minimum-presentation carrier excess `e = M_min-h`.

* easy: `e ≤ 3`, and the intrinsic carrier graph diameter is at most exactly `e`;
* hard: `e ≥ 4`, and for the effective minimum-presentation witness the
  remaining neutral-rank defect is at most `(n-d)-4`.

This is a per-step resource statement, not an amortized whole-walk bound. -/
theorem rowCircuit_commonFace_easy_cost_or_hard_neutral_defect
    (hsmall : SmallExcessHpolyBound)
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hx : x ∈ Hpoly a b)
    (hcirc : IsRowCircuit a (y - x)) :
    (commonFacePresentationExcess a b x y ≤ 3 ∧
      DiamLE (commonFace a b x y) (commonFacePresentationExcess a b x y)) ∨
    ∃ e : Fin (commonFaceMinSubpresentationCount a b x y) ↪ Fin n,
      Hpoly
          (fun j => HirschCommonFace.commonFaceA a b x y (e j))
          (fun j => HirschCommonFace.commonFaceB a b x y (e j)) =
        Hpoly
          (HirschCommonFace.commonFaceA a b x y)
          (HirschCommonFace.commonFaceB a b x y) ∧
      let F : Finset (Fin n) :=
        (Finset.univ.map e) ∩ HirschCommonFace.commonFaceEffectiveRows a b x y
      F.card = commonFaceMinSubpresentationCount a b x y ∧
      4 ≤ commonFacePresentationExcess a b x y ∧
      ((commonFaceDim a b x y - 1) -
        Module.finrank ℝ
          (((HirschCommonFace.rowEvalMap a
            (F ∩ Finset.univ.filter (fun i =>
              a i ≠ 0 ∧ ⟪a i, y - x⟫ = 0))).domRestrict
            (HirschCommonFace.commonDirection a b x y)).range)) ≤
        (n - d) - 4 := by
  classical
  by_cases heasy : commonFacePresentationExcess a b x y ≤ 3
  · exact Or.inl ⟨heasy,
      commonFace_diamLE_minPresentationExcess_of_le_three
        hsmall a b x y hbd hx heasy⟩
  · right
    have hhard : 4 ≤ commonFacePresentationExcess a b x y := by omega
    obtain ⟨e, heq, hFcard, hbudget⟩ :=
      rowCircuit_commonFace_minSubpresentation_excess_defect_of_bounded
        a b x y hbd hx hcirc
    refine ⟨e, heq, ?_⟩
    let F : Finset (Fin n) :=
      (Finset.univ.map e) ∩ HirschCommonFace.commonFaceEffectiveRows a b x y
    let D : ℕ :=
      ((HirschCommonFace.commonFaceDim a b x y - 1) -
        Module.finrank ℝ
          (((HirschCommonFace.rowEvalMap a
            (((Finset.univ.map e) ∩
              HirschCommonFace.commonFaceEffectiveRows a b x y) ∩
              Finset.univ.filter (fun i =>
                a i ≠ 0 ∧ ⟪a i, y - x⟫ = 0))).domRestrict
            (HirschCommonFace.commonDirection a b x y)).range))
    have hbudgetD :
        (commonFaceMinSubpresentationCount a b x y -
            HirschCommonFace.commonFaceDim a b x y) + D ≤ n - d := by
      simpa [D] using hbudget
    have hdim :
        commonFaceDim a b x y = HirschCommonFace.commonFaceDim a b x y := by
      rfl
    have hhardPub :
        4 ≤ commonFaceMinSubpresentationCount a b x y -
          HirschCommonFace.commonFaceDim a b x y := by
      simpa [commonFacePresentationExcess, hdim] using hhard
    have hD : D ≤ (n - d) - 4 := by
      omega
    refine ⟨?_, hhard, ?_⟩
    · simpa [F] using hFcard
    · simpa [D, F, hdim] using hD

#print axioms rowCircuit_commonFace_easy_cost_or_hard_neutral_defect

end HirschCircuitLocalization
