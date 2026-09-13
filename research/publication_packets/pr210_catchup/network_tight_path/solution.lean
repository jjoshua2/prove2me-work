import Mathlib
set_option autoImplicit false
noncomputable section

theorem solution
    (n : ℕ) (u v : ℕ → ℝ) (cost : Fin n → ℝ) (C : ℝ)
    (hu : ∀ i : Fin n, u (i.val + 1) - u i.val = cost i)
    (hv : ∀ i : Fin n, v (i.val + 1) - v i.val ≤ cost i)
    (hvtarget : v n - v 0 = C)
    (hutarget : u n - u 0 ≤ C) :
    u n - u 0 = C := by
  have hdom : ∀ k : ℕ, k ≤ n → v k - v 0 ≤ u k - u 0 := by
    intro k
    induction k with
    | zero =>
        intro _
        simp
    | succ k ih =>
        intro hk
        have hkprev : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
        have hprev := ih hkprev
        have hkn : k < n := Nat.lt_of_succ_le hk
        let i : Fin n := ⟨k, hkn⟩
        have hvi := hv i
        have hui := hu i
        change v (k + 1) - v k ≤ cost i at hvi
        change u (k + 1) - u k = cost i at hui
        nlinarith
  have hlower := hdom n (le_rfl)
  rw [hvtarget] at hlower
  exact le_antisymm hutarget hlower

#print axioms solution
