import Mathlib
import Solutions.PolynomialCircuitInjectiveDeletionSavings
import Solutions.PolynomialOneRowDeletionCubicCircuitWalk

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschDeletion

open HirschPolynomialAccess
open HirschCircuitLocalization

/-- The exact `h-1` neutral-rank theorem applies inside the potentially
unbounded one-row deletion outer because that outer has an injective row map. -/
theorem rowCircuit_neutral_rank_on_deletion_commonDirection_eq_sub_one
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b)
    (j : Fin n)
    (u v : EuclideanSpace ℝ (Fin d))
    (hcirc : IsRowCircuit (rowsWithout a j) (v - u)) :
    Module.finrank ℝ
        (((rowEvalMap (rowsWithout a j)
          (circuitNeutralRows (rowsWithout a j) (v - u))).domRestrict
          (commonDirection (rowsWithout a j) (rhsWithout b j) u v)).range) =
      commonFaceDim (rowsWithout a j) (rhsWithout b j) u v - 1 := by
  exact
    rowCircuit_neutral_rank_on_commonDirection_eq_commonFaceDim_sub_one_of_injective
      (rowsWithout a j) (rhsWithout b j) u v
      (rowMap_rowsWithout_injective_of_bounded a b hbd x hx j) hcirc

/-- The complete exact excess/defect/savings identity is valid inside the
unbounded deletion presentation itself.  Thus the same carrier accounting used
in the bounded parent survives deletion; boundedness is not lost at the rank
bookkeeping layer. -/
theorem rowCircuit_selected_excess_defect_savings_identity_of_one_row_deletion
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b)
    (j : Fin n)
    (u v : EuclideanSpace ℝ (Fin d))
    (hcirc : IsRowCircuit (rowsWithout a j) (v - u))
    (F : Finset (Fin (Fintype.card {i : Fin n // i ≠ j})))
    (hF : F ⊆ effectiveRowsOnSubspace (rowsWithout a j)
      (commonDirection (rowsWithout a j) (rhsWithout b j) u v))
    (hface : commonFaceDim (rowsWithout a j) (rhsWithout b j) u v ≤ F.card) :
    let W := commonDirection (rowsWithout a j) (rhsWithout b j) u v
    let h := commonFaceDim (rowsWithout a j) (rhsWithout b j) u v
    let E := effectiveRowsOnSubspace (rowsWithout a j) W
    let Z := circuitNeutralRows (rowsWithout a j) (v - u)
    let delta := (h - 1) -
      Module.finrank ℝ
        (((rowEvalMap (rowsWithout a j) (F ∩ Z)).domRestrict W).range)
    (F.card - h) + delta +
      (Fintype.card {i : Fin n // i ≠ j} + h - (E.card + d)) +
      ((E \ F) \ Z).card + (((E \ F) ∩ Z).card - delta) =
        Fintype.card {i : Fin n // i ≠ j} - d := by
  exact
    rowCircuit_selected_excess_defect_savings_identity_of_injective
      (rowsWithout a j) (rhsWithout b j) u v
      (rowMap_rowsWithout_injective_of_bounded a b hbd x hx j)
      hcirc F hF hface

/-- Strengthened resource inequality on the one-row deletion presentation:
selected presentation excess, neutral defect, and every omitted nonneutral
effective row are all charged against the deletion outer's own row excess. -/
theorem rowCircuit_selected_excess_defect_add_nonneutral_savings_le_of_one_row_deletion
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b)
    (j : Fin n)
    (u v : EuclideanSpace ℝ (Fin d))
    (hcirc : IsRowCircuit (rowsWithout a j) (v - u))
    (F : Finset (Fin (Fintype.card {i : Fin n // i ≠ j})))
    (hF : F ⊆ effectiveRowsOnSubspace (rowsWithout a j)
      (commonDirection (rowsWithout a j) (rhsWithout b j) u v))
    (hface : commonFaceDim (rowsWithout a j) (rhsWithout b j) u v ≤ F.card) :
    let W := commonDirection (rowsWithout a j) (rhsWithout b j) u v
    let h := commonFaceDim (rowsWithout a j) (rhsWithout b j) u v
    let E := effectiveRowsOnSubspace (rowsWithout a j) W
    let Z := circuitNeutralRows (rowsWithout a j) (v - u)
    let delta := (h - 1) -
      Module.finrank ℝ
        (((rowEvalMap (rowsWithout a j) (F ∩ Z)).domRestrict W).range)
    (F.card - h) + delta + ((E \ F) \ Z).card ≤
      Fintype.card {i : Fin n // i ≠ j} - d := by
  exact
    rowCircuit_selected_excess_defect_add_nonneutral_savings_le_of_injective
      (rowsWithout a j) (rhsWithout b j) u v
      (rowMap_rowsWithout_injective_of_bounded a b hbd x hx j)
      hcirc F hF hface

#print axioms rowCircuit_neutral_rank_on_deletion_commonDirection_eq_sub_one
#print axioms rowCircuit_selected_excess_defect_savings_identity_of_one_row_deletion
#print axioms rowCircuit_selected_excess_defect_add_nonneutral_savings_le_of_one_row_deletion

end HirschDeletion
