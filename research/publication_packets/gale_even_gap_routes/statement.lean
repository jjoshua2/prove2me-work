import Mathlib
set_option autoImplicit false

theorem Hirsch.gale_even_gap_exchange_routes (m d : ℕ) (S T : Finset (Fin m))
    (hS : S.card = d) (hT : T.card = d)
    (hGS : ∀ i ∉ S, ∀ j ∉ S, i < j →
      (S.filter (fun s => i < s ∧ s < j)).card % 2 = 0)
    (hGT : ∀ i ∉ T, ∀ j ∉ T, i < j →
      (T.filter (fun s => i < s ∧ s < j)).card % 2 = 0) :
    ∃ L : ℕ, L ≤ 2*(m-d)+1 ∧ ∃ p : ℕ → Finset (Fin m),
      p 0 = S ∧ p L = T ∧
      (∀ t, t ≤ L → (p t).card = d ∧
        ∀ i ∉ p t, ∀ j ∉ p t, i < j →
          ((p t).filter (fun s => i < s ∧ s < j)).card % 2 = 0) ∧
      ∀ t, t < L → p t ≠ p (t+1) ∧ (p t ∩ p (t+1)).card + 1 = d := by sorry
