import Mathlib
import Solutions.PolynomialMinCarrierExcessRouting
import Solutions.PolynomialCircuitSaturatedPhaseBlocker

open scoped BigOperators RealInnerProductSpace
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- Route-ordered specialization of the carrier savings dichotomy on an actual
minimum equivalent carrier presentation.

For a maximal row-circuit step which remains inside one fixed slack-routing
phase, choose a minimum original-row presentation of the common carrier. Then
either its presentation-excess plus selected neutral-rank defect is strictly
below the ambient row excess, or one of those minimum selected rows is a
specific same-phase blocker: it is target-only for the step, strictly slack at
the final target, was already trapped at the phase reference, and its slack
drops from positive to zero across the step.

The strict alternative is the recursive lower-resource case.  The blocker
alternative is the equality/saturation case.  This theorem does not itself
bound how often the same blocker may recur later in a phase. -/
theorem rowCircuitStep_minPresentation_same_phase_strict_budget_or_selected_target_positive_blocker
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hstep : RowCircuitStep a b x y)
    (hv : v ∈ Hpoly a b)
    (Mphase : ℝ) (hMphase : 0 ≤ Mphase) (r : Fin n → ℝ)
    (heqx :
      HirschCircuit.phaseProgressSet Mphase (HirschCircuit.slack a b v) r =
        HirschCircuit.phaseProgressSet Mphase (HirschCircuit.slack a b v)
          (HirschCircuit.slack a b x))
    (heqy :
      HirschCircuit.phaseProgressSet Mphase (HirschCircuit.slack a b v) r =
        HirschCircuit.phaseProgressSet Mphase (HirschCircuit.slack a b v)
          (HirschCircuit.slack a b y)) :
    let Mc := commonFaceMinSubpresentationCount a b x y
    ∃ e : Fin Mc ↪ Fin n,
      Hpoly
          (fun j => HirschCommonFace.commonFaceA a b x y (e j))
          (fun j => HirschCommonFace.commonFaceB a b x y (e j)) =
        Hpoly
          (HirschCommonFace.commonFaceA a b x y)
          (HirschCommonFace.commonFaceB a b x y) ∧
      let F : Finset (Fin n) :=
        (Finset.univ.map e) ∩ HirschCommonFace.commonFaceEffectiveRows a b x y
      F.card = Mc ∧
      ((Mc - commonFaceDim a b x y) +
          ((commonFaceDim a b x y - 1) -
            Module.finrank ℝ
              (((rowEvalMap a (F ∩ circuitNeutralRows a (y - x))).domRestrict
                (commonDirection a b x y)).range)) <
        n - d ∨
       ∃ i : Fin n,
          i ∈ F ∧
          i ∈ targetOnlyRows a b x y ∧
          ⟪a i, v⟫ < b i ∧
          r i ≤ Mphase * HirschCircuit.slack a b v i ∧
          HirschCircuit.slack a b y i = 0 ∧
          HirschCircuit.slack a b y i < HirschCircuit.slack a b x i) := by
  classical
  let Mc := commonFaceMinSubpresentationCount a b x y
  obtain ⟨e, heq, hFeq⟩ :=
    commonFace_minSubpresentation_effective_witness_of_feasible
      a b x y hstep.1
  refine ⟨e, heq, ?_⟩
  let F : Finset (Fin n) :=
    (Finset.univ.map e) ∩ HirschCommonFace.commonFaceEffectiveRows a b x y
  have hFM : F.card = Mc := by
    simpa [F, Mc] using hFeq
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
      _ = F.card := by simpa [Mc] using hFM.symm
  have hbudget := rowCircuit_selectedEffectiveRows_excess_defect_of_bounded
    a b x y hbd hstep.1 hstep.2.2.1 F hFint hface
  refine ⟨hFM, ?_⟩
  by_cases hstrict :
      (F.card - commonFaceDim a b x y) +
          ((commonFaceDim a b x y - 1) -
            Module.finrank ℝ
              (((rowEvalMap a (F ∩ circuitNeutralRows a (y - x))).domRestrict
                (commonDirection a b x y)).range)) <
        n - d
  · left
    simpa [Mc, hFM] using hstrict
  · right
    have hsat :
        (F.card - commonFaceDim a b x y) +
            ((commonFaceDim a b x y - 1) -
              Module.finrank ℝ
                (((rowEvalMap a (F ∩ circuitNeutralRows a (y - x))).domRestrict
                  (commonDirection a b x y)).range)) =
          n - d := by
      omega
    exact
      rowCircuitStep_saturated_same_phase_selected_target_positive_blocker
        a b x y v hbd hstep hv F hFint hface hsat
        Mphase hMphase r heqx heqy

#print axioms rowCircuitStep_minPresentation_same_phase_strict_budget_or_selected_target_positive_blocker

end HirschCircuitLocalization
