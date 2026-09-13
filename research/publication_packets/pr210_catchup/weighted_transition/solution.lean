import Mathlib
open scoped BigOperators
set_option autoImplicit false
noncomputable section

theorem solution
    {ι : Type*} [Fintype ι]
    (L : ℕ) (weight demand : ι → ℝ) (change : ι → Fin L → ℝ)
    (hw : ∀ i, 0 ≤ weight i)
    (hd : ∀ i, demand i ≤ ∑ j, change i j)
    (hstep : ∀ j, (∑ i, weight i * change i j) ≤ 1) :
    (∑ i, weight i * demand i) ≤ (L : ℝ) := by
  calc
    (∑ i, weight i * demand i) ≤ ∑ i, weight i * ∑ j, change i j :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hd i) (hw i))
    _ = ∑ j, ∑ i, weight i * change i j := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ _j : Fin L, (1 : ℝ) := Finset.sum_le_sum (fun j _ => hstep j)
    _ = (L : ℝ) := by simp

#print axioms solution
