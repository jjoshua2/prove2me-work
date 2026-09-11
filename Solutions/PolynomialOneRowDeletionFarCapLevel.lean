import Mathlib
import Solutions.PolynomialOneRowDeletionCapBounded

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschDeletion

/-- A bounded nonempty parent admits an explicit cap level strictly beyond the
entire parent.  We take a closed-ball radius `r` around the origin and bound
`-⟪a_i,x⟫` by `‖a_i‖ r` termwise; adding one gives strict separation from the
cap hyperplane.

At this level the one-row-deletion outer is bounded by the previous theorem and
contains the whole original parent strictly below its cap. -/
theorem exists_far_deletion_cap_level
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hne : (Hpoly a b).Nonempty)
    (j : Fin n) :
    ∃ M : ℝ,
      Bornology.IsBounded (deletionCappedOuter a b j M) ∧
      (∀ x ∈ Hpoly a b, x ∈ deletionCappedOuter a b j M) ∧
      (∀ x ∈ Hpoly a b, deletionCapValue a j x < M) := by
  classical
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨r, hr⟩ := hbd.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  have hr0 : 0 ≤ r := by
    have hxball := Metric.mem_closedBall.mp (hr hx0)
    have hdist : 0 ≤ dist x0 0 := dist_nonneg
    linarith
  let I := {i : Fin n // i ≠ j}
  let C : ℝ := (∑ i : I, ‖a i.1‖) * r
  let M : ℝ := C + 1
  have hcap_le : ∀ x ∈ Hpoly a b, deletionCapValue a j x ≤ C := by
    intro x hx
    have hxball := Metric.mem_closedBall.mp (hr hx)
    have hxnorm : ‖x‖ ≤ r := by
      simpa [dist_zero_right] using hxball
    unfold deletionCapValue
    calc
      (∑ i : I, -⟪a i.1, x⟫) ≤ ∑ i : I, |⟪a i.1, x⟫| := by
        apply Finset.sum_le_sum
        intro i hi
        exact neg_le_abs _
      _ ≤ ∑ i : I, ‖a i.1‖ * ‖x‖ := by
        apply Finset.sum_le_sum
        intro i hi
        exact abs_real_inner_le_norm _ _
      _ ≤ ∑ i : I, ‖a i.1‖ * r := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left hxnorm (norm_nonneg _)
      _ = C := by
        simp [C, Finset.sum_mul]
  refine ⟨M, ?_, ?_, ?_⟩
  · exact deletionCappedOuter_isBounded_of_bounded_parent
      a b hbd x0 hx0 j M
  · intro x hx
    refine ⟨?_, ?_⟩
    · intro i hij
      exact hx i
    · have hle := hcap_le x hx
      dsimp [M]
      linarith
  · intro x hx
    have hle := hcap_le x hx
    dsimp [M]
    linarith

/-- Once a cap level contains the original parent, reinserting the deleted row
recovers the parent exactly.  If the containment is strict in cap value, the
cap face is disjoint from the parent. -/
theorem deletionCappedOuter_inter_deletedRow_eq_parent
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (j : Fin n) (M : ℝ)
    (hcontain : ∀ x ∈ Hpoly a b, x ∈ deletionCappedOuter a b j M) :
    deletionCappedOuter a b j M ∩ {x | ⟪a j, x⟫ ≤ b j} = Hpoly a b := by
  ext x
  constructor
  · rintro ⟨hxcap, hxj⟩ i
    by_cases hij : i = j
    · subst i
      exact hxj
    · exact hxcap.1 i hij
  · intro hx
    exact ⟨hcontain x hx, hx j⟩

/-- For a strictly containing cap, its cap hyperplane is exterior to the final
parent. -/
theorem deletion_cap_face_disjoint_parent
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (j : Fin n) (M : ℝ)
    (hstrict : ∀ x ∈ Hpoly a b, deletionCapValue a j x < M) :
    (Hpoly a b ∩ {x | deletionCapValue a j x = M}) = ∅ := by
  ext x
  constructor
  · rintro ⟨hx, heq⟩
    have hlt := hstrict x hx
    rw [heq] at hlt
    exact False.elim (lt_irrefl M hlt)
  · intro hx
    exact False.elim hx

#print axioms exists_far_deletion_cap_level
#print axioms deletionCappedOuter_inter_deletedRow_eq_parent
#print axioms deletion_cap_face_disjoint_parent

end HirschDeletion
