import Mathlib
set_option autoImplicit false

theorem Hirsch.alternating_complement_exchange_routes (m r : ℕ) (h k : Fin r → ℕ)
    (hh : StrictMono h) (hk : StrictMono k)
    (hhm : ∀ i, h i < m) (hkm : ∀ i, k i < m)
    (hphase : ∃ b : ℕ, b < 2 ∧ ∀ i, h i % 2 = (b + i.val) % 2)
    (kphase : ∃ b : ℕ, b < 2 ∧ ∀ i, k i % 2 = (b + i.val) % 2) :
    ∃ L : ℕ, L ≤ 2*r+1 ∧ ∃ p : ℕ → Finset ℕ,
      p 0 = Finset.univ.image h ∧ p L = Finset.univ.image k ∧
      (∀ t, t ≤ L → p t ⊆ Finset.range m ∧ (p t).card = r ∧
        (Finset.range m \ p t).card = m-r ∧
        ∃ a : Fin r → ℕ, StrictMono a ∧ (∀ i, a i < m) ∧
          (∃ b : ℕ, b < 2 ∧ ∀ i, a i % 2 = (b + i.val) % 2) ∧
          Finset.univ.image a = p t) ∧
      (∀ t, t < L → p t ≠ p (t+1) ∧ (p t ∩ p (t+1)).card + 1 = r ∧
        (Finset.range m \ p t) ≠ (Finset.range m \ p (t+1)) ∧
        ((Finset.range m \ p t) ∩ (Finset.range m \ p (t+1))).card + 1 = m-r) := by sorry
