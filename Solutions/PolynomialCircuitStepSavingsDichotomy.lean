import Mathlib
import Solutions.PolynomialMinCarrierExcessRouting
import Solutions.PolynomialCircuitSaturatedBlocker

open scoped BigOperators RealInnerProductSpace
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- Every maximal row-circuit step, for any selected effective carrier rows,
has one of two outcomes: the excess-plus-neutral-defect resource is strictly
below the ambient row-excess budget, or the selected rows already contain a
genuinely new target-only blocker.

This removes the equality premise from the saturated-blocker interface. It is
still a one-step structural dichotomy, not an amortized routing theorem. -/
theorem rowCircuitStep_selected_strict_budget_or_targetOnlyRow
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hstep : RowCircuitStep a b x y)
    (F : Finset (Fin n))
    (hF : F ⊆ effectiveRowsOnSubspace a (commonDirection a b x y))
    (hface : commonFaceDim a b x y ≤ F.card) :
    (F.card - commonFaceDim a b x y) +
        ((commonFaceDim a b x y - 1) -
          Module.finrank ℝ
            (((rowEvalMap a (F ∩ circuitNeutralRows a (y - x))).domRestrict
              (commonDirection a b x y)).range)) <
      n - d ∨
    ∃ i : Fin n, i ∈ F ∧ i ∈ targetOnlyRows a b x y := by
  have hsave :=
    rowCircuit_selected_excess_defect_add_nonneutral_savings_le_of_bounded
      a b x y hbd hstep.1 hstep.2.2.1 F hF hface
  dsimp only at hsave
  by_cases hstrict :
      (F.card - commonFaceDim a b x y) +
          ((commonFaceDim a b x y - 1) -
            Module.finrank ℝ
              (((rowEvalMap a (F ∩ circuitNeutralRows a (y - x))).domRestrict
                (commonDirection a b x y)).range)) <
        n - d
  · exact Or.inl hstrict
  · right
    have hsat :
        (F.card - commonFaceDim a b x y) +
            ((commonFaceDim a b x y - 1) -
              Module.finrank ℝ
                (((rowEvalMap a (F ∩ circuitNeutralRows a (y - x))).domRestrict
                  (commonDirection a b x y)).range)) =
          n - d := by
      omega
    exact rowCircuitStep_saturated_selected_targetOnlyRow
      a b x y hbd hstep F hF hface hsat

/-- Minimum-presentation specialization.  Every maximal row-circuit step admits
an exact minimum equivalent common-carrier presentation whose selected effective
rows either have strict excess/defect slack or contain a target-only blocker.

The same witness is retained in both alternatives, so a later phase argument
can reason about actual minimum carrier rows rather than an unrelated selected
set. -/
theorem rowCircuitStep_minPresentation_strict_budget_or_selected_targetOnlyRow
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hstep : RowCircuitStep a b x y) :
    let M := commonFaceMinSubpresentationCount a b x y
    ∃ e : Fin M ↪ Fin n,
      Hpoly
          (fun j => HirschCommonFace.commonFaceA a b x y (e j))
          (fun j => HirschCommonFace.commonFaceB a b x y (e j)) =
        Hpoly
          (HirschCommonFace.commonFaceA a b x y)
          (HirschCommonFace.commonFaceB a b x y) ∧
      let F : Finset (Fin n) :=
        (Finset.univ.map e) ∩ HirschCommonFace.commonFaceEffectiveRows a b x y
      F.card = M ∧
      ((M - commonFaceDim a b x y) +
          ((commonFaceDim a b x y - 1) -
            Module.finrank ℝ
              (((rowEvalMap a (F ∩ circuitNeutralRows a (y - x))).domRestrict
                (commonDirection a b x y)).range)) <
        n - d ∨
       ∃ i : Fin n, i ∈ F ∧ i ∈ targetOnlyRows a b x y) := by
  classical
  let M := commonFaceMinSubpresentationCount a b x y
  obtain ⟨e, heq, hFeq⟩ :=
    commonFace_minSubpresentation_effective_witness_of_feasible
      a b x y hstep.1
  refine ⟨e, heq, ?_⟩
  let F : Finset (Fin n) :=
    (Finset.univ.map e) ∩ HirschCommonFace.commonFaceEffectiveRows a b x y
  have hFM : F.card = M := by
    simpa [F, M] using hFeq
  have hFpub : F ⊆ HirschCommonFace.commonFaceEffectiveRows a b x y :=
    Finset.inter_subset_right
  have hFint : F ⊆ effectiveRowsOnSubspace a (commonDirection a b x y) := by
    rw [effectiveRowsOn_commonDirection_eq_publicCommonFaceEffectiveRows]
    exact hFpub
  have hdimM := commonFaceDim_le_minSubpresentation_of_bounded_feasible
    a b x y hbd hstep.1
  have hface : commonFaceDim a b x y ≤ F.card := by
    calc
      commonFaceDim a b x y ≤ commonFaceMinSubpresentationCount a b x y := hdimM
      _ = F.card := by simpa [M] using hFM.symm
  have hsplit := rowCircuitStep_selected_strict_budget_or_targetOnlyRow
    a b x y hbd hstep F hFint hface
  refine ⟨hFM, ?_⟩
  simpa [M, F] using hsplit

#print axioms rowCircuitStep_selected_strict_budget_or_targetOnlyRow
#print axioms rowCircuitStep_minPresentation_strict_budget_or_selected_targetOnlyRow

end HirschCircuitLocalization
