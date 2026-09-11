import Mathlib
import Solutions.PolynomialOneRowDeletionPointedness

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschDeletion

/-- Explicit scalar cap functional for the outer H-polyhedron obtained by
deleting row `j`: negative sum of the remaining row evaluations. -/
noncomputable def deletionCapValue
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (j : Fin n)
    (r : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i : {i : Fin n // i ≠ j}, (-⟪a i.1, r⟫)

/-- If the remaining-row map is injective, the explicit cap functional is
strictly positive on every nonzero direction satisfying all remaining
recession inequalities.

This is the constructive pointedness-to-cap step from the ordinary exterior-cap
argument: every summand is nonnegative, and a zero total would force every
remaining row evaluation to vanish, contradicting injectivity. -/
theorem deletionCapValue_pos_of_injective
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (j : Fin n)
    (hinj : Function.Injective (rowMapWithout a j))
    (r : EuclideanSpace ℝ (Fin d)) (hr : r ≠ 0)
    (hrec : ∀ i : Fin n, i ≠ j → ⟪a i, r⟫ ≤ 0) :
    0 < deletionCapValue a j r := by
  classical
  have hnonneg : ∀ i : {i : Fin n // i ≠ j},
      0 ≤ -⟪a i.1, r⟫ := by
    intro i
    exact neg_nonneg.mpr (hrec i.1 i.2)
  have hsum_nonneg : 0 ≤ deletionCapValue a j r := by
    exact Finset.sum_nonneg (fun i _ => hnonneg i)
  by_contra hnot
  have hle0 : deletionCapValue a j r ≤ 0 := le_of_not_gt hnot
  have hsum0 : deletionCapValue a j r = 0 := le_antisymm hle0 hsum_nonneg
  have hzero : ∀ i : {i : Fin n // i ≠ j}, ⟪a i.1, r⟫ = 0 := by
    intro i
    have hsingle : -⟪a i.1, r⟫ ≤ deletionCapValue a j r := by
      unfold deletionCapValue
      exact Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ i)
    rw [hsum0] at hsingle
    have hz : -⟪a i.1, r⟫ = 0 := le_antisymm hsingle (hnonneg i)
    linarith
  have hmap : rowMapWithout a j r = 0 := by
    funext i
    simpa [rowMapWithout] using hzero i
  have hr0 : r = 0 := by
    apply hinj
    simpa using hmap
  exact hr hr0

/-- For a nonempty bounded H-presentation, deleting any row gives an outer
system whose explicit negative-row-sum functional is strictly positive on every
nonzero recession direction of that deletion outer.

Together with `rowMapWithout_injective_of_bounded`, this supplies an explicit
coercive cap direction; the still-unformalized part of the universal far-cap
construction is choosing a sufficiently large level and classifying the new cap
vertices/rays. -/
theorem deletionCapValue_pos_on_recession_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b)
    (j : Fin n)
    (r : EuclideanSpace ℝ (Fin d)) (hr : r ≠ 0)
    (hrec : ∀ i : Fin n, i ≠ j → ⟪a i, r⟫ ≤ 0) :
    0 < deletionCapValue a j r := by
  exact deletionCapValue_pos_of_injective a j
    (rowMapWithout_injective_of_bounded a b hbd x hx j) r hr hrec

#print axioms deletionCapValue_pos_of_injective
#print axioms deletionCapValue_pos_on_recession_of_bounded

end HirschDeletion
