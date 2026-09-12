import Mathlib
import Solutions.PolynomialCommonFaceInjectivePresentations
import Solutions.PolynomialCommonFaceIrredundantModel
import Solutions.PolynomialCircuitInjectiveDeletionSavings
import Solutions.PolynomialCircuitStepProgress
import Solutions.CircuitPhaseBlockerPersistence
import Solutions.PolynomialCircuitIrredundantMinCarrierDichotomy

open scoped BigOperators RealInnerProductSpace
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 6000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- Under row-map injectivity, saturation of presentation excess plus selected
neutral defect forces every effective nonneutral row to be retained.  This is
the pointed analogue of the bounded saturation lemma. -/
theorem rowCircuit_saturated_selected_contains_effective_nonneutral_of_injective
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (hcirc : IsRowCircuit a (y - x))
    (F : Finset (Fin n))
    (hF : F ⊆ effectiveRowsOnSubspace a (commonDirection a b x y))
    (hface : commonFaceDim a b x y ≤ F.card)
    (hsat :
      (F.card - commonFaceDim a b x y) +
        ((commonFaceDim a b x y - 1) -
          Module.finrank ℝ
            (((rowEvalMap a (F ∩ circuitNeutralRows a (y - x))).domRestrict
              (commonDirection a b x y)).range)) = n - d)
    (i : Fin n)
    (hiE : i ∈ effectiveRowsOnSubspace a (commonDirection a b x y))
    (hinon : ⟪a i, y - x⟫ ≠ 0) :
    i ∈ F := by
  have hsave :=
    rowCircuit_selected_excess_defect_add_nonneutral_savings_le_of_injective
      a b x y hinj hcirc F hF hface
  dsimp only at hsave
  have hcount :
      (((effectiveRowsOnSubspace a (commonDirection a b x y)) \ F) \
        circuitNeutralRows a (y - x)).card = 0 := by
    omega
  by_contra hiF
  have hiZ : i ∉ circuitNeutralRows a (y - x) := by
    intro hi
    exact hinon (Finset.mem_filter.1 hi).2.2
  have himem : i ∈
      ((effectiveRowsOnSubspace a (commonDirection a b x y) \ F) \
        circuitNeutralRows a (y - x)) :=
    Finset.mem_sdiff.2 ⟨Finset.mem_sdiff.2 ⟨hiE, hiF⟩, hiZ⟩
  have hpos : 0 <
      (((effectiveRowsOnSubspace a (commonDirection a b x y)) \ F) \
        circuitNeutralRows a (y - x)).card :=
    Finset.card_pos.2 ⟨i, himem⟩
  omega

/-- A saturated selected presentation for a maximal circuit step in an
injective finite H-presentation contains a genuine new target blocker. -/
theorem rowCircuitStep_saturated_selected_target_blocker_of_injective
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (hstep : RowCircuitStep a b x y)
    (F : Finset (Fin n))
    (hF : F ⊆ effectiveRowsOnSubspace a (commonDirection a b x y))
    (hface : commonFaceDim a b x y ≤ F.card)
    (hsat :
      (F.card - commonFaceDim a b x y) +
        ((commonFaceDim a b x y - 1) -
          Module.finrank ℝ
            (((rowEvalMap a (F ∩ circuitNeutralRows a (y - x))).domRestrict
              (commonDirection a b x y)).range)) = n - d) :
    ∃ i : Fin n,
      i ∈ F ∧ a i ≠ 0 ∧ ⟪a i, y⟫ = b i ∧ 0 < ⟪a i, y - x⟫ := by
  obtain ⟨i, hia, hiy, hipos⟩ :=
    rowCircuitStep_exists_target_blocking_row a b x y hstep
  have hgW : y - x ∈ commonDirection a b x y := by
    apply LinearMap.mem_ker.2
    funext j
    have hj := (Finset.mem_filter.1 j.2).2
    change ⟪a j.1, y - x⟫ = 0
    rw [inner_sub_right, hj.2.2, hj.2.1, sub_self]
  have hiE : i ∈ effectiveRowsOnSubspace a (commonDirection a b x y) := by
    apply Finset.mem_filter.2
    exact ⟨Finset.mem_univ i, ⟨⟨y - x, hgW⟩, ne_of_gt hipos⟩⟩
  have hiFmem := rowCircuit_saturated_selected_contains_effective_nonneutral_of_injective
    a b x y hinj hstep.2.2.1 F hF hface hsat i hiE (ne_of_gt hipos)
  exact ⟨i, hiFmem, hia, hiy, hipos⟩

/-- The saturated blocker receives the same ordered same-phase interpretation
as in the bounded parent: selected, target-only, strictly slack at the final
target, already trapped at the phase reference, and newly zero at the step
endpoint. -/
theorem rowCircuitStep_saturated_same_phase_selected_target_positive_blocker_of_injective
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y v : EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (hstep : RowCircuitStep a b x y)
    (hv : v ∈ Hpoly a b)
    (F : Finset (Fin n))
    (hF : F ⊆ effectiveRowsOnSubspace a (commonDirection a b x y))
    (hface : commonFaceDim a b x y ≤ F.card)
    (hsat :
      (F.card - commonFaceDim a b x y) +
        ((commonFaceDim a b x y - 1) -
          Module.finrank ℝ
            (((rowEvalMap a (F ∩ circuitNeutralRows a (y - x))).domRestrict
              (commonDirection a b x y)).range)) = n - d)
    (M : ℝ) (hM : 0 ≤ M) (r : Fin n → ℝ)
    (heqx :
      HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v) r =
        HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v)
          (HirschCircuit.slack a b x))
    (heqy :
      HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v) r =
        HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v)
          (HirschCircuit.slack a b y)) :
    ∃ i : Fin n,
      i ∈ F ∧
      i ∈ targetOnlyRows a b x y ∧
      ⟪a i, v⟫ < b i ∧
      r i ≤ M * HirschCircuit.slack a b v i ∧
      HirschCircuit.slack a b y i = 0 ∧
      HirschCircuit.slack a b y i < HirschCircuit.slack a b x i := by
  obtain ⟨i, hiF, hia, hiy, hipos⟩ :=
    rowCircuitStep_saturated_selected_target_blocker_of_injective
      a b x y hinj hstep F hF hface hsat
  have hxne : ⟪a i, x⟫ ≠ b i := by
    intro hix
    rw [inner_sub_right, hiy, hix, sub_self] at hipos
    exact (lt_irrefl 0 hipos)
  have hiTargetOnly : i ∈ targetOnlyRows a b x y := by
    simp [targetOnlyRows, hia, hxne, hiy]
  have hsy : HirschCircuit.slack a b y i = 0 := by
    simp [HirschCircuit.slack, hiy]
  have hsxpos : 0 < HirschCircuit.slack a b x i := by
    rw [inner_sub_right, hiy] at hipos
    simpa [HirschCircuit.slack] using hipos
  have hdown :
      HirschCircuit.slack a b y i < HirschCircuit.slack a b x i := by
    rw [hsy]
    exact hsxpos
  have hsvnonneg : ∀ j, 0 ≤ HirschCircuit.slack a b v j := by
    intro j
    change 0 ≤ b j - ⟪a j, v⟫
    exact sub_nonneg.mpr (hv j)
  obtain ⟨hsvne, htrap⟩ :=
    HirschCircuit.same_phase_zero_blocker_is_trapped_positive
      M (HirschCircuit.slack a b v) r
        (HirschCircuit.slack a b x) (HirschCircuit.slack a b y)
      hM hsvnonneg heqx heqy i hsy hdown
  have hsvpos : 0 < HirschCircuit.slack a b v i :=
    lt_of_le_of_ne (hsvnonneg i) (Ne.symm hsvne)
  have hvstrict : ⟪a i, v⟫ < b i := by
    change 0 < b i - ⟪a i, v⟫ at hsvpos
    exact sub_pos.mp hsvpos
  exact ⟨i, hiF, hiTargetOnly, hvstrict, htrap, hsy, hdown⟩

/-- Pointed/injective version of the irredundant minimum-carrier same-phase
strict/blocker dichotomy.

The proof uses no ambient boundedness: #153 supplies the exact injective savings
identity, while common-face minimum presentations inherit injectivity and hence
the row-count lower bound from the pointed presentation transfer theorem. -/
theorem rowCircuitStep_irredundant_minPresentation_same_phase_strict_budget_or_essential_trapped_blocker_of_injective
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y v : EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (HirschCircuit.rowMap a))
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
  have hdimM : commonFaceDim a b x y ≤ m :=
    commonFaceDim_le_subpresentation_of_injective
      a b x y hstep.1 hinj e heq
  have hface : commonFaceDim a b x y ≤ F.card := by
    simpa [F] using hdimM
  have hsave :=
    rowCircuit_selected_excess_defect_add_nonneutral_savings_le_of_injective
      a b x y hinj hstep.2.2.1 F hFint hface
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
      rowCircuitStep_saturated_same_phase_selected_target_positive_blocker_of_injective
        a b x y v hinj hstep hv F hFint hface hsat M hM r heqx heqy
    obtain ⟨j, _hj, hji⟩ := Finset.mem_map.1 hiF
    subst i
    obtain ⟨q, hqtight, hqstrict⟩ :=
      HirschRowCount.exists_single_tight_point_of_irredundant
        (fun k => HirschCommonFace.commonFaceA a b x y (e k))
        (fun k => HirschCommonFace.commonFaceB a b x y (e k))
        hirr hstrictRows j
    exact ⟨j, hiTargetOnly, hvstrict, htrap, hsy, hdown,
      q, hqtight, hqstrict⟩

#print axioms rowCircuit_saturated_selected_contains_effective_nonneutral_of_injective
#print axioms rowCircuitStep_saturated_selected_target_blocker_of_injective
#print axioms rowCircuitStep_saturated_same_phase_selected_target_positive_blocker_of_injective
#print axioms rowCircuitStep_irredundant_minPresentation_same_phase_strict_budget_or_essential_trapped_blocker_of_injective

end HirschCircuitLocalization
