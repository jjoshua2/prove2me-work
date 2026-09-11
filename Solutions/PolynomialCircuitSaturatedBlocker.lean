import Mathlib
import Solutions.PolynomialCircuitDeletionSavings
import Solutions.PolynomialCircuitStepProgress

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- If presentation excess plus selected neutral-rank defect uses the entire
ambient row-excess budget, then every effective row which is nonneutral on the
circuit displacement must be retained. Otherwise that omitted row would
contribute one unit to the exact nonneutral-deletion saving. -/
theorem rowCircuit_saturated_selected_contains_effective_nonneutral
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b)) (hx : x ∈ Hpoly a b)
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
    rowCircuit_selected_excess_defect_add_nonneutral_savings_le_of_bounded
      a b x y hbd hx hcirc F hF hface
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

/-- A saturated selected presentation for a maximal circuit step must contain a
genuinely new target blocker. This is the first direct bridge from exact
carrier-savings accounting to ordered maximal-step progress. -/
theorem rowCircuitStep_saturated_selected_target_blocker
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
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
  have hiFmem := rowCircuit_saturated_selected_contains_effective_nonneutral
    a b x y hbd hstep.1 hstep.2.2.1 F hF hface hsat i hiE (ne_of_gt hipos)
  exact ⟨i, hiFmem, hia, hiy, hipos⟩

/-- Geometric packaging: the retained blocker is selected and is tight only at
the destination. Hence every saturated maximal step contributes a selected
`targetOnlyRows` certificate, although this alone does not make such rows
persistent across different carriers. -/
theorem rowCircuitStep_saturated_selected_targetOnlyRow
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
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
    ∃ i : Fin n, i ∈ F ∧ i ∈ targetOnlyRows a b x y := by
  obtain ⟨i, hiF, hia, hiy, hipos⟩ :=
    rowCircuitStep_saturated_selected_target_blocker
      a b x y hbd hstep F hF hface hsat
  have hxle := hstep.1 i
  have hxne : ⟪a i, x⟫ ≠ b i := by
    intro hix
    rw [inner_sub_right, hiy, hix, sub_self] at hipos
    exact (lt_irrefl 0 hipos)
  refine ⟨i, hiF, ?_⟩
  simp [targetOnlyRows, hia, hxne, hiy]

#print axioms rowCircuit_saturated_selected_contains_effective_nonneutral
#print axioms rowCircuitStep_saturated_selected_target_blocker
#print axioms rowCircuitStep_saturated_selected_targetOnlyRow

end HirschCircuitLocalization
