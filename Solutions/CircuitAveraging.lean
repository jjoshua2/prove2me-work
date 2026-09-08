import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace HirschCircuit

/-- If at most `M` real scores sum to a positive quantity `W`, some score is at
least the average lower bound `W/M`. This is the finite selector used for both
norm-reduction and elimination circuit choices. -/
theorem exists_mem_ge_average
    {α : Type*} (xs : List α) (f : α → ℝ) (M : ℕ) (W : ℝ)
    (hM : 0 < M) (hlen : xs.length ≤ M) (hW : 0 < W)
    (hsum : (xs.map f).sum = W) :
    ∃ x ∈ xs, W / (M : ℝ) ≤ f x := by
  by_contra hnone
  push Not at hnone
  have hall : ∀ x ∈ xs, f x < W / (M : ℝ) := by
    intro x hx
    exact lt_of_not_ge (hnone x hx)
  have hsumlt : (xs.map f).sum < (xs.length : ℝ) * (W / (M : ℝ)) := by
    induction xs with
    | nil =>
        simp at hsum
    | cons a xs ih =>
        have ha : f a < W / (M : ℝ) := hall a (by simp)
        have htail : ∀ x ∈ xs, f x < W / (M : ℝ) := by
          intro x hx
          exact hall x (by simp [hx])
        have hih := ih htail
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
          Nat.cast_one]
        nlinarith
  have hlenR : (xs.length : ℝ) ≤ (M : ℝ) := by exact_mod_cast hlen
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have havg : 0 < W / (M : ℝ) := div_pos hW hMR
  have hupper : (xs.length : ℝ) * (W / (M : ℝ)) ≤ W := by
    have hmul := mul_le_mul_of_nonneg_right hlenR (le_of_lt havg)
    have hcancel : (M : ℝ) * (W / (M : ℝ)) = W := by
      field_simp [ne_of_gt hMR]
    rwa [hcancel] at hmul
  linarith [hsumlt, hupper, hsum]

/-- A nonempty exact decomposition of a nonzero vector has a nonempty list of
pieces. -/
theorem list_nonempty_of_sum_ne_zero {α : Type*} [AddMonoid α]
    (xs : List α) (h : xs.sum ≠ 0) : xs ≠ [] := by
  intro hx
  subst xs
  simp at h

#print axioms exists_mem_ge_average
#print axioms list_nonempty_of_sum_ne_zero

end HirschCircuit
