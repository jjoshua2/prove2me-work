import Mathlib
import Solutions.PolynomialCircuitStepSavingsDichotomy
import Solutions.PolynomialCircuitSaturatedPhaseBlocker
import Solutions.PolynomialCommonFaceIntrinsicRowCount
import Solutions.PolynomialCommonFaceIrredundantModel

open scoped BigOperators RealInnerProductSpace
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- Every maximal row-circuit step admits an equivalent common-carrier row model
which is simultaneously irredundant, strictly feasible, and minimum-cardinality.
On that same model, either presentation excess plus selected neutral-rank defect
is strictly below the ambient row-excess budget, or one of its indispensable
rows is target-only for the step.

In the blocker alternative we also expose the standard irredundancy witness: a
coordinate point where that blocker row alone is tight among the minimum model
rows. This turns the selected blocker from a mere retained inequality into an
essential carrier row suitable for later facet/section arguments. -/
theorem rowCircuitStep_irredundant_minPresentation_strict_budget_or_essential_targetOnlyRow
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hstep : RowCircuitStep a b x y) :
    ∃ m : ℕ, m ≤ n ∧ ∃ e : Fin m ↪ Fin n,
      Hpoly
          (fun j => HirschCommonFace.commonFaceA a b x y (e j))
          (fun j => HirschCommonFace.commonFaceB a b x y (e j)) =
        Hpoly
          (HirschCommonFace.commonFaceA a b x y)
          (HirschCommonFace.commonFaceB a b x y) ∧
      RowPresentationIrredundant
          (fun j => HirschCommonFace.commonFaceA a b x y (e j))
          (fun j => HirschCommonFace.commonFaceB a b x y (e j)) ∧
      StrictlyFeasibleRows
          (fun j => HirschCommonFace.commonFaceA a b x y (e j))
          (fun j => HirschCommonFace.commonFaceB a b x y (e j)) ∧
      commonFaceMinSubpresentationCount a b x y = m ∧
      let F : Finset (Fin n) := Finset.univ.map e
      ((m - commonFaceDim a b x y) +
          ((commonFaceDim a b x y - 1) -
            Module.finrank ℝ
              (((rowEvalMap a (F ∩ circuitNeutralRows a (y - x))).domRestrict
                (commonDirection a b x y)).range)) <
        n - d ∨
       ∃ j : Fin m,
         e j ∈ targetOnlyRows a b x y ∧
         ∃ q : EuclideanSpace ℝ (Fin (commonFaceDim a b x y)),
           ⟪HirschCommonFace.commonFaceA a b x y (e j), q⟫ =
             HirschCommonFace.commonFaceB a b x y (e j) ∧
           ∀ k : Fin m, k ≠ j →
             ⟪HirschCommonFace.commonFaceA a b x y (e k), q⟫ <
               HirschCommonFace.commonFaceB a b x y (e k)) := by
  classical
  obtain ⟨m, hm, e, heq, hirr, hstrictRows⟩ :=
    commonFace_coord_irredundant_strict_subpresentation
      a b x y hstep.1 hstep.2.1
  have hmin : commonFaceMinSubpresentationCount a b x y = m :=
    commonFace_minCount_eq_irredundant_subpresentation
      a b x y e heq hirr hstrictRows
  refine ⟨m, hm, e, heq, hirr, hstrictRows, hmin, ?_⟩
  let F : Finset (Fin n) := Finset.univ.map e
  have hzeroFull :
      (0 : EuclideanSpace ℝ (Fin (commonFaceDim a b x y))) ∈
        Hpoly
          (HirschCommonFace.commonFaceA a b x y)
          (HirschCommonFace.commonFaceB a b x y) := by
    apply (mem_commonFace_coord_iff a b x y 0).2
    simpa [commonFacePoint] using commonFace_u_mem a b x y hstep.1
  have hzeroSub :
      (0 : EuclideanSpace ℝ (Fin (commonFaceDim a b x y))) ∈
        Hpoly
          (fun j => HirschCommonFace.commonFaceA a b x y (e j))
          (fun j => HirschCommonFace.commonFaceB a b x y (e j)) := by
    intro j
    exact hzeroFull (e j)
  have hnonzero :
      ∀ j : Fin m, HirschCommonFace.commonFaceA a b x y (e j) ≠ 0 :=
    HirschCircuit.irredundant_rows_nonzero_of_mem
      (fun j => HirschCommonFace.commonFaceA a b x y (e j))
      (fun j => HirschCommonFace.commonFaceB a b x y (e j))
      hirr 0 hzeroSub
  have hFint : F ⊆ effectiveRowsOnSubspace a (commonDirection a b x y) := by
    rw [effectiveRowsOn_commonDirection_eq_coordinateEffectiveRows]
    intro i hiF
    obtain ⟨j, _hj, hji⟩ := Finset.mem_map.1 hiF
    subst i
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hnonzero j⟩
  have hface : commonFaceDim a b x y ≤ F.card := by
    have hdimM := commonFaceDim_le_minSubpresentation_of_bounded_feasible
      a b x y hbd hstep.1
    calc
      commonFaceDim a b x y ≤ commonFaceMinSubpresentationCount a b x y := hdimM
      _ = m := hmin
      _ = F.card := by simp [F]
  have hsplit := rowCircuitStep_selected_strict_budget_or_targetOnlyRow
    a b x y hbd hstep F hFint hface
  rcases hsplit with hbudget | ⟨i, hiF, hiTargetOnly⟩
  · left
    simpa [F] using hbudget
  · right
    obtain ⟨j, _hj, hji⟩ := Finset.mem_map.1 hiF
    subst i
    obtain ⟨q, hqtight, hqstrict⟩ :=
      HirschRowCount.exists_single_tight_point_of_irredundant
        (fun k => HirschCommonFace.commonFaceA a b x y (e k))
        (fun k => HirschCommonFace.commonFaceB a b x y (e k))
        hirr hstrictRows j
    exact ⟨j, hiTargetOnly, q, hqtight, hqstrict⟩

/-- Same minimum irredundant model, enriched by the actual phase order of the
cubic circuit walk. If the excess/defect budget is not strict, an indispensable
minimum-model blocker is target-only for the step, strictly slack at the fixed
final target, already trapped at the phase reference, and its slack drops to
zero across the step.

The final single-tight coordinate witness certifies that this blocker is not a
redundant artifact of the chosen minimum presentation. -/
theorem rowCircuitStep_irredundant_minPresentation_same_phase_strict_budget_or_essential_trapped_blocker
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hstep : RowCircuitStep a b x y)
    (hv : v ∈ Hpoly a b)
    (M : ℝ) (hM : 0 ≤ M) (r : Fin n → ℝ)
    (heqx :
      HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v) r =
        HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v)
          (HirschCircuit.slack a b x))
    (heqy :
      HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v) r =
        HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v)
          (HirschCircuit.slack a b y)) :
    ∃ m : ℕ, m ≤ n ∧ ∃ e : Fin m ↪ Fin n,
      Hpoly
          (fun j => HirschCommonFace.commonFaceA a b x y (e j))
          (fun j => HirschCommonFace.commonFaceB a b x y (e j)) =
        Hpoly
          (HirschCommonFace.commonFaceA a b x y)
          (HirschCommonFace.commonFaceB a b x y) ∧
      RowPresentationIrredundant
          (fun j => HirschCommonFace.commonFaceA a b x y (e j))
          (fun j => HirschCommonFace.commonFaceB a b x y (e j)) ∧
      StrictlyFeasibleRows
          (fun j => HirschCommonFace.commonFaceA a b x y (e j))
          (fun j => HirschCommonFace.commonFaceB a b x y (e j)) ∧
      commonFaceMinSubpresentationCount a b x y = m ∧
      let F : Finset (Fin n) := Finset.univ.map e
      ((m - commonFaceDim a b x y) +
          ((commonFaceDim a b x y - 1) -
            Module.finrank ℝ
              (((rowEvalMap a (F ∩ circuitNeutralRows a (y - x))).domRestrict
                (commonDirection a b x y)).range)) <
        n - d ∨
       ∃ j : Fin m,
         e j ∈ targetOnlyRows a b x y ∧
         ⟪a (e j), v⟫ < b (e j) ∧
         r (e j) ≤ M * HirschCircuit.slack a b v (e j) ∧
         HirschCircuit.slack a b y (e j) = 0 ∧
         HirschCircuit.slack a b y (e j) < HirschCircuit.slack a b x (e j) ∧
         ∃ q : EuclideanSpace ℝ (Fin (commonFaceDim a b x y)),
           ⟪HirschCommonFace.commonFaceA a b x y (e j), q⟫ =
             HirschCommonFace.commonFaceB a b x y (e j) ∧
           ∀ k : Fin m, k ≠ j →
             ⟪HirschCommonFace.commonFaceA a b x y (e k), q⟫ <
               HirschCommonFace.commonFaceB a b x y (e k)) := by
  classical
  obtain ⟨m, hm, e, heq, hirr, hstrictRows⟩ :=
    commonFace_coord_irredundant_strict_subpresentation
      a b x y hstep.1 hstep.2.1
  have hmin : commonFaceMinSubpresentationCount a b x y = m :=
    commonFace_minCount_eq_irredundant_subpresentation
      a b x y e heq hirr hstrictRows
  refine ⟨m, hm, e, heq, hirr, hstrictRows, hmin, ?_⟩
  let F : Finset (Fin n) := Finset.univ.map e
  have hzeroFull :
      (0 : EuclideanSpace ℝ (Fin (commonFaceDim a b x y))) ∈
        Hpoly
          (HirschCommonFace.commonFaceA a b x y)
          (HirschCommonFace.commonFaceB a b x y) := by
    apply (mem_commonFace_coord_iff a b x y 0).2
    simpa [commonFacePoint] using commonFace_u_mem a b x y hstep.1
  have hzeroSub :
      (0 : EuclideanSpace ℝ (Fin (commonFaceDim a b x y))) ∈
        Hpoly
          (fun j => HirschCommonFace.commonFaceA a b x y (e j))
          (fun j => HirschCommonFace.commonFaceB a b x y (e j)) := by
    intro j
    exact hzeroFull (e j)
  have hnonzero :
      ∀ j : Fin m, HirschCommonFace.commonFaceA a b x y (e j) ≠ 0 :=
    HirschCircuit.irredundant_rows_nonzero_of_mem
      (fun j => HirschCommonFace.commonFaceA a b x y (e j))
      (fun j => HirschCommonFace.commonFaceB a b x y (e j))
      hirr 0 hzeroSub
  have hFint : F ⊆ effectiveRowsOnSubspace a (commonDirection a b x y) := by
    rw [effectiveRowsOn_commonDirection_eq_coordinateEffectiveRows]
    intro i hiF
    obtain ⟨j, _hj, hji⟩ := Finset.mem_map.1 hiF
    subst i
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hnonzero j⟩
  have hface : commonFaceDim a b x y ≤ F.card := by
    have hdimM := commonFaceDim_le_minSubpresentation_of_bounded_feasible
      a b x y hbd hstep.1
    calc
      commonFaceDim a b x y ≤ commonFaceMinSubpresentationCount a b x y := hdimM
      _ = m := hmin
      _ = F.card := by simp [F]
  have hsave :=
    rowCircuit_selected_excess_defect_add_nonneutral_savings_le_of_bounded
      a b x y hbd hstep.1 hstep.2.2.1 F hFint hface
  dsimp only at hsave
  by_cases hbudget :
      (F.card - commonFaceDim a b x y) +
          ((commonFaceDim a b x y - 1) -
            Module.finrank ℝ
              (((rowEvalMap a (F ∩ circuitNeutralRows a (y - x))).domRestrict
                (commonDirection a b x y)).range)) <
        n - d
  · left
    simpa [F] using hbudget
  · right
    have hsat :
        (F.card - commonFaceDim a b x y) +
            ((commonFaceDim a b x y - 1) -
              Module.finrank ℝ
                (((rowEvalMap a (F ∩ circuitNeutralRows a (y - x))).domRestrict
                  (commonDirection a b x y)).range)) =
          n - d := by
      omega
    obtain ⟨i, hiF, hiTargetOnly, hvstrict, htrap, hsy, hdown⟩ :=
      rowCircuitStep_saturated_same_phase_selected_target_positive_blocker
        a b x y v hbd hstep hv F hFint hface hsat M hM r heqx heqy
    obtain ⟨j, _hj, hji⟩ := Finset.mem_map.1 hiF
    subst i
    obtain ⟨q, hqtight, hqstrict⟩ :=
      HirschRowCount.exists_single_tight_point_of_irredundant
        (fun k => HirschCommonFace.commonFaceA a b x y (e k))
        (fun k => HirschCommonFace.commonFaceB a b x y (e k))
        hirr hstrictRows j
    exact ⟨j, hiTargetOnly, hvstrict, htrap, hsy, hdown,
      q, hqtight, hqstrict⟩

#print axioms rowCircuitStep_irredundant_minPresentation_strict_budget_or_essential_targetOnlyRow
#print axioms rowCircuitStep_irredundant_minPresentation_same_phase_strict_budget_or_essential_trapped_blocker

end HirschCircuitLocalization
