import Mathlib
import Solutions.PolynomialCircuitBoundedNeutralRank
import Solutions.PolynomialCommonFaceEffectiveRows

/-!
# Exact savings in nonvertex circuit-carrier defect accounting

The old inequality `(|F|-h) + defect <= n-d` drops two kinds of savings:
rows disappearing on the carrier beyond its codimension, and redundant neutral
rank among the effective rows removed from a selected presentation. In
particular, every discarded *nonneutral* effective row saves one full unit.

This file proves an exact three-term slack identity and its strictness/equality
criteria. These are one-carrier accounting theorems, not a monotonicity or
polynomial graph-routing theorem. `F` need not be an equivalent presentation;
when it is a minimum equivalent presentation, existing boundedness lemmas give
`h <= |F|`. Neither endpoint needs to be a vertex.
-/

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- Keep the neutral-deletion count instead of weakening it to all deletions.
The source is merely feasible; boundedness supplies exact ambient circuit rank. -/
theorem rowCircuit_selected_defect_le_discarded_neutral_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b)) (hx : x ∈ Hpoly a b)
    (hcirc : IsRowCircuit a (y - x))
    (F : Finset (Fin n))
    (hF : F ⊆ effectiveRowsOnSubspace a (commonDirection a b x y)) :
    let W := commonDirection a b x y
    let E := effectiveRowsOnSubspace a W
    let Z := circuitNeutralRows a (y - x)
    (commonFaceDim a b x y - 1) -
        Module.finrank ℝ (((rowEvalMap a (F ∩ Z)).domRestrict W).range) ≤
      ((E \ F) ∩ Z).card := by
  classical
  let W := commonDirection a b x y
  let E := effectiveRowsOnSubspace a W
  let Z := circuitNeutralRows a (y - x)
  have hST : F ∩ Z ⊆ Z ∩ E := by
    intro i hi
    exact Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hi).2,
      hF (Finset.mem_inter.1 hi).1⟩
  have hfull : Module.finrank ℝ
      (((rowEvalMap a (Z ∩ E)).domRestrict W).range) =
      Module.finrank ℝ W - 1 := by
    rw [show E = effectiveRowsOnSubspace a W from rfl,
      restricted_rowEval_effective_rank_eq]
    exact rowCircuit_neutral_rank_on_commonDirection_eq_commonFaceDim_sub_one_of_bounded
      a b hbd x y hx hcirc
  have h := restricted_rowEval_defect_le_deleted a W (F ∩ Z) (Z ∩ E) hST hfull
  have heq : (Z ∩ E) \ (F ∩ Z) = (E \ F) ∩ Z := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rw [heq] at h
  exact h

/-- Exact decomposition of the unused ambient excess into three nonnegative
savings: disappearance surplus `kappa`, discarded nonneutral rows `s`, and
neutral deletion redundancy `t`. All subtractions are justified in the proof.

`e_F + delta + kappa + s + t = n-d`.

A small number of high-excess carriers is NOT sufficient for a polynomial
routing bound: their own graph costs still need an independent bound. -/
theorem rowCircuit_selected_excess_defect_savings_identity_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b)) (hx : x ∈ Hpoly a b)
    (hcirc : IsRowCircuit a (y - x))
    (F : Finset (Fin n))
    (hF : F ⊆ effectiveRowsOnSubspace a (commonDirection a b x y))
    (hface : commonFaceDim a b x y ≤ F.card) :
    let W := commonDirection a b x y
    let h := commonFaceDim a b x y
    let E := effectiveRowsOnSubspace a W
    let Z := circuitNeutralRows a (y - x)
    let delta := (h - 1) -
      Module.finrank ℝ (((rowEvalMap a (F ∩ Z)).domRestrict W).range)
    (F.card - h) + delta +
      (n + h - (E.card + d)) +
      ((E \ F) \ Z).card + (((E \ F) ∩ Z).card - delta) = n - d := by
  classical
  let W := commonDirection a b x y
  let h := commonFaceDim a b x y
  let E := effectiveRowsOnSubspace a W
  let Z := circuitNeutralRows a (y - x)
  let delta := (h - 1) -
    Module.finrank ℝ (((rowEvalMap a (F ∩ Z)).domRestrict W).range)
  have hdef : delta ≤ ((E \ F) ∩ Z).card :=
    rowCircuit_selected_defect_le_discarded_neutral_of_bounded a b x y hbd hx hcirc F hF
  have hbudget : E.card + d ≤ n + h :=
    commonDirection_effectiveRows_card_add_dim_le_rows_add_faceDim a b x y
  have hdn := rows_ge_dimension_of_bounded a b hbd x hx
  have hcard : (E \ F).card + F.card = E.card :=
    Finset.card_sdiff_add_card_eq_card hF
  have hsplit : ((E \ F) \ Z).card + ((E \ F) ∩ Z).card = (E \ F).card :=
    Finset.card_sdiff_add_card_inter (E \ F) Z
  change (F.card - h) + delta + (n + h - (E.card + d)) +
    ((E \ F) \ Z).card + (((E \ F) ∩ Z).card - delta) = n - d
  change h ≤ F.card at hface
  omega

/-- Strengthened resource bound: every omitted nonneutral effective row gives
one extra unit of certified slack beyond presentation excess and neutral defect. -/
theorem rowCircuit_selected_excess_defect_add_nonneutral_savings_le_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b)) (hx : x ∈ Hpoly a b)
    (hcirc : IsRowCircuit a (y - x))
    (F : Finset (Fin n))
    (hF : F ⊆ effectiveRowsOnSubspace a (commonDirection a b x y))
    (hface : commonFaceDim a b x y ≤ F.card) :
    let W := commonDirection a b x y
    let h := commonFaceDim a b x y
    let E := effectiveRowsOnSubspace a W
    let Z := circuitNeutralRows a (y - x)
    let delta := (h - 1) -
      Module.finrank ℝ (((rowEvalMap a (F ∩ Z)).domRestrict W).range)
    (F.card - h) + delta + ((E \ F) \ Z).card ≤ n - d := by
  have hid := rowCircuit_selected_excess_defect_savings_identity_of_bounded
    a b x y hbd hx hcirc F hF hface
  dsimp only at hid ⊢
  omega

/-- The old budget is saturated precisely when all three explicit savings
vanish. The last equality says every discarded neutral row costs a unit of rank. -/
theorem rowCircuit_selected_budget_saturated_iff_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b)) (hx : x ∈ Hpoly a b)
    (hcirc : IsRowCircuit a (y - x))
    (F : Finset (Fin n))
    (hF : F ⊆ effectiveRowsOnSubspace a (commonDirection a b x y))
    (hface : commonFaceDim a b x y ≤ F.card) :
    let W := commonDirection a b x y
    let h := commonFaceDim a b x y
    let E := effectiveRowsOnSubspace a W
    let Z := circuitNeutralRows a (y - x)
    let delta := (h - 1) -
      Module.finrank ℝ (((rowEvalMap a (F ∩ Z)).domRestrict W).range)
    (F.card - h) + delta = n - d ↔
      E.card + d = n + h ∧
      ((E \ F) \ Z).card = 0 ∧
      ((E \ F) ∩ Z).card = delta := by
  have hid := rowCircuit_selected_excess_defect_savings_identity_of_bounded
    a b x y hbd hx hcirc F hF hface
  have hdef := rowCircuit_selected_defect_le_discarded_neutral_of_bounded
    a b x y hbd hx hcirc F hF
  have hbudget := commonDirection_effectiveRows_card_add_dim_le_rows_add_faceDim a b x y
  dsimp only at hid hdef ⊢
  omega

#print axioms rowCircuit_selected_defect_le_discarded_neutral_of_bounded
#print axioms rowCircuit_selected_excess_defect_savings_identity_of_bounded
#print axioms rowCircuit_selected_excess_defect_add_nonneutral_savings_le_of_bounded
#print axioms rowCircuit_selected_budget_saturated_iff_of_bounded

end HirschCircuitLocalization
