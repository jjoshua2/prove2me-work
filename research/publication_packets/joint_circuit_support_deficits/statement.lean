import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.joint_external_circuit_support_and_zero_deficit
    (m r k : ℕ) (a : Fin m → Fin r → Fin k → ℝ)
    (w : (Fin m ⊕ (Fin r × Option (Fin k))) → ℝ)
    (hw : ∀ q, 0 ≤ w q)
    (hkernel : ∀ l j, -(∑ i, w (.inl i) * a i l j) -
      w (.inr (l, some j)) + w (.inr (l, none)) = 0)
    (hexternal : ∃ i, w (.inl i) ≠ 0)
    (hminimal : ∀ y : (Fin m ⊕ (Fin r × Option (Fin k))) → ℝ,
      (∀ q, 0 ≤ y q) →
      (∀ l j, -(∑ i, y (.inl i) * a i l j) -
        y (.inr (l, some j)) + y (.inr (l, none)) = 0) →
      y ≠ 0 → Function.support y ⊆ Function.support w →
        Function.support w ⊆ Function.support y) :
    ∀ l,
      (0 ≤ w (.inr (l, none)) ∧
        (∀ j, (∑ i, w (.inl i) * a i l j) ≤ w (.inr (l, none))) ∧
        (w (.inr (l, none)) = 0 ∨
          ∃ j, w (.inr (l, none)) = ∑ i, w (.inl i) * a i l j)) ∧
      ∀ h : Fin m → ℝ, (∀ i, 0 ≤ h i) → (∀ i j, a i l j ≤ h i) →
        0 ≤ (∑ i, w (.inl i) * h i) - w (.inr (l, none)) ∧
        (((∑ i, w (.inl i) * h i) - w (.inr (l, none)) = 0) ↔
          ∃ q : Option (Fin k), ∀ i, 0 < w (.inl i) →
            (match q with | none => 0 | some j => a i l j) = h i) := by sorry
