import Mathlib
open scoped BigOperators

theorem Hirsch.interleaved_moment_minimal_nonfaces (k m : ℕ) (a : Fin m → ℝ) (ha : Function.Injective a)
    (l r : Fin (k+1) → Fin m)
    (hpair : ∀ i, a (l i) < a (r i))
    (hsep : ∀ i j, i < j → a (r i) < a (l j)) :
    let row : (Fin (2*k) → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin (2*k),
        (a i ^ (j.val+1) - (∑ z, a z ^ (j.val+1)) / (m : ℝ)) * x j
    let L : Finset (Fin m) := Finset.univ.image l
    let R : Finset (Fin m) := Finset.univ.image r
    L.card = k+1 ∧ R.card = k+1 ∧ Disjoint L R ∧
    (∀ x : Fin (2*k) → ℝ, (∀ i, row x i ≤ 1) →
      (∃ i ∈ L, row x i < 1) ∧ (∃ i ∈ R, row x i < 1)) ∧
    ∀ S : Finset (Fin m), (S ⊂ L ∨ S ⊂ R) →
      ∃ x : Fin (2*k) → ℝ, ∀ i, row x i ≤ 1 ∧ (row x i = 1 ↔ i ∈ S) := by sorry
