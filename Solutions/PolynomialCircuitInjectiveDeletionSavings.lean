import Mathlib
import Solutions.PolynomialCircuitInjectiveNeutralRank
import Solutions.PolynomialCircuitDeletionSavings

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- The selected neutral-rank defect is paid by discarded neutral rows under
row-map injectivity alone.  No boundedness or checkpoint vertex hypothesis is
needed. -/
theorem rowCircuit_selected_defect_le_discarded_neutral_of_injective
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (HirschCircuit.rowMap a))
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
    exact rowCircuit_neutral_rank_on_subspace_eq_dim_sub_one_of_injective
      a hinj (y - x) hcirc W (by
        change rowEvalMap a (commonSourceRows a b x y) (y - x) = 0
        funext i
        have hi := (Finset.mem_filter.1 i.2).2
        change ⟪a i.1, y - x⟫ = 0
        rw [inner_sub_right, hi.2.2, hi.2.1, sub_self])
  have h := restricted_rowEval_defect_le_deleted a W (F ∩ Z) (Z ∩ E) hST hfull
  have heq : (Z ∩ E) \ (F ∩ Z) = (E \ F) ∩ Z := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rw [heq] at h
  exact h

/-- Exact decomposition of the unused row excess for any injective
presentation.  This is the bounded deletion-savings identity with boundedness
replaced by its actual linear-algebra consequence.

`e_F + delta + kappa + s + t = n-d`. -/
theorem rowCircuit_selected_excess_defect_savings_identity_of_injective
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (HirschCircuit.rowMap a))
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
    rowCircuit_selected_defect_le_discarded_neutral_of_injective
      a b x y hinj hcirc F hF
  have hbudget : E.card + d ≤ n + h :=
    commonDirection_effectiveRows_card_add_dim_le_rows_add_faceDim a b x y
  have hdn : d ≤ n := rows_ge_dimension_of_injective a hinj
  have hcard : (E \ F).card + F.card = E.card :=
    Finset.card_sdiff_add_card_eq_card hF
  have hsplit : ((E \ F) \ Z).card + ((E \ F) ∩ Z).card = (E \ F).card :=
    Finset.card_sdiff_add_card_inter (E \ F) Z
  change (F.card - h) + delta + (n + h - (E.card + d)) +
    ((E \ F) \ Z).card + (((E \ F) ∩ Z).card - delta) = n - d
  change h ≤ F.card at hface
  omega

/-- Every omitted nonneutral effective row gives one additional certified unit
of slack, now valid on injective pointed presentations as well as bounded ones. -/
theorem rowCircuit_selected_excess_defect_add_nonneutral_savings_le_of_injective
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (HirschCircuit.rowMap a))
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
  have hid := rowCircuit_selected_excess_defect_savings_identity_of_injective
    a b x y hinj hcirc F hF hface
  dsimp only at hid ⊢
  omega

/-- Saturation of the old excess/defect budget has the same exact equality
criterion under injectivity alone. -/
theorem rowCircuit_selected_budget_saturated_iff_of_injective
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (HirschCircuit.rowMap a))
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
  have hid := rowCircuit_selected_excess_defect_savings_identity_of_injective
    a b x y hinj hcirc F hF hface
  have hdef := rowCircuit_selected_defect_le_discarded_neutral_of_injective
    a b x y hinj hcirc F hF
  have hbudget := commonDirection_effectiveRows_card_add_dim_le_rows_add_faceDim
    a b x y
  dsimp only at hid hdef ⊢
  omega

#print axioms rowCircuit_selected_defect_le_discarded_neutral_of_injective
#print axioms rowCircuit_selected_excess_defect_savings_identity_of_injective
#print axioms rowCircuit_selected_excess_defect_add_nonneutral_savings_le_of_injective
#print axioms rowCircuit_selected_budget_saturated_iff_of_injective

end HirschCircuitLocalization
