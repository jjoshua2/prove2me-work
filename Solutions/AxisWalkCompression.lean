import Mathlib

noncomputable section

namespace HirschAxisWalk

/-- If the values of a function differ at the two ends of a finite walk, some
consecutive pair has different values. -/
lemma exists_changed_step {V α : Type*} [DecidableEq α]
    (f : V → α) (w : ℕ → V) (N : ℕ)
    (hne : f (w 0) ≠ f (w N)) :
    ∃ j < N, f (w j) ≠ f (w (j + 1)) := by
  by_contra h
  push_neg at h
  have hind : ∀ k ≤ N, f (w k) = f (w 0) := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
        have hkN : k < N := by omega
        have hstep := h k hkN
        exact hstep.symm.trans (ih (by omega))
  exact hne ((hind N (Nat.le_refl N)).symm)

/-- Delete one stationary step from a padded walk.  This is deliberately
relation-agnostic: no symmetry or transitivity of `R` is required. -/
lemma compress_stationary_step {V : Type*}
    (R : V → V → Prop) (w : ℕ → V) (N j : ℕ)
    (hj : j < N + 1)
    (hstat : w j = w (j + 1))
    (hw : ∀ k < N + 1, w k = w (k + 1) ∨ R (w k) (w (k + 1))) :
    ∃ w' : ℕ → V,
      w' 0 = w 0 ∧
      w' N = w (N + 1) ∧
      ∀ k < N, w' k = w' (k + 1) ∨ R (w' k) (w' (k + 1)) := by
  let w' : ℕ → V := fun k => if k ≤ j then w k else w (k + 1)
  refine ⟨w', ?_, ?_, ?_⟩
  · simp [w']
  · have hjN : j ≤ N := by omega
    by_cases hNj : N ≤ j
    · have hNj' : N = j := le_antisymm hNj hjN
      subst j
      simp [w', hstat]
    · have : ¬ N ≤ j := hNj
      simp [w', this]
  · intro k hk
    by_cases hkj : k < j
    · have hk_le : k ≤ j := by omega
      have hk1_le : k + 1 ≤ j := by omega
      simpa [w', hk_le, hk1_le] using hw k (by omega)
    · by_cases hkeq : k = j
      · subst k
        have hjN : j < N := by omega
        have hj_le : j ≤ j := Nat.le_refl j
        have hj1_not : ¬ j + 1 ≤ j := by omega
        have hnext := hw (j + 1) (by omega)
        rw [← hstat] at hnext
        simpa [w', hj_le, hj1_not] using hnext
      · have hjk : j < k := by omega
        have hk_not : ¬ k ≤ j := by omega
        have hk1_not : ¬ k + 1 ≤ j := by omega
        simpa [w', hk_not, hk1_not] using hw (k + 1) (by omega)

end HirschAxisWalk
