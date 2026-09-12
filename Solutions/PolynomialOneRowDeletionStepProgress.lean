import Mathlib
import Solutions.PolynomialCircuitInjectiveStepProgress
import Solutions.PolynomialOneRowDeletionCubicCircuitWalk

open scoped RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschDeletion

open HirschPolynomialAccess
open HirschCircuitLocalization

/-- Maximal row-circuit steps in the potentially unbounded one-row deletion
outer satisfy the same source-carrier bound as in a bounded H-polytope.

The row count is the deletion presentation's actual retained-row count. -/
theorem rowCircuitStep_commonFaceDim_source_bound_of_one_row_deletion
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (z : EuclideanSpace ℝ (Fin d)) (hz : z ∈ Hpoly a b)
    (j : Fin n)
    (x y : EuclideanSpace ℝ (Fin d))
    (hstep : RowCircuitStep (rowsWithout a j) (rhsWithout b j) x y) :
    commonFaceDim (rowsWithout a j) (rhsWithout b j) x y + d ≤
      Fintype.card {i : Fin n // i ≠ j} +
        commonFaceDim (rowsWithout a j) (rhsWithout b j) x x := by
  exact rowCircuitStep_commonFaceDim_source_bound_of_injective
    (rowsWithout a j) (rhsWithout b j) x y
    (rowMap_rowsWithout_injective_of_bounded a b hbd z hz j) hstep

/-- Strict destination-self-face progress for maximal circuit steps in the
unbounded deletion outer. -/
theorem rowCircuitStep_target_commonFaceDim_progress_of_one_row_deletion
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (z : EuclideanSpace ℝ (Fin d)) (hz : z ∈ Hpoly a b)
    (j : Fin n)
    (x y : EuclideanSpace ℝ (Fin d))
    (hstep : RowCircuitStep (rowsWithout a j) (rhsWithout b j) x y) :
    commonFaceDim (rowsWithout a j) (rhsWithout b j) y y + d + 1 ≤
      Fintype.card {i : Fin n // i ≠ j} +
        commonFaceDim (rowsWithout a j) (rhsWithout b j) x x := by
  exact rowCircuitStep_target_commonFaceDim_progress_of_injective
    (rowsWithout a j) (rhsWithout b j) x y
    (rowMap_rowsWithout_injective_of_bounded a b hbd z hz j) hstep

#print axioms rowCircuitStep_commonFaceDim_source_bound_of_one_row_deletion
#print axioms rowCircuitStep_target_commonFaceDim_progress_of_one_row_deletion

end HirschDeletion
