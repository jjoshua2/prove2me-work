import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.zonotope_selected_direction_lower_bound (d m r : ℕ) (w : Fin m → (Fin d → ℝ))
    (selected : Fin r → Fin m)
    (hnonzero : ∀ i, w (selected i) ≠ 0)
    (hseparate : ∀ i j : Fin r, ∀ c : ℝ,
      w (selected i) = c • w (selected j) → i = j) :
    let Z : Set (Fin d → ℝ) := {x | ∃ s : Fin m → ℝ,
      (∀ i, 0 ≤ s i ∧ s i ≤ 1) ∧ (∑ i : Fin m, s i • w i) = x}
    ∃ u v : Fin d → ℝ,
      u ∈ Z.extremePoints ℝ ∧ v ∈ Z.extremePoints ℝ ∧
      u + v = ∑ i : Fin m, w i ∧
      ∀ L : ℕ, ∀ p : Fin (L+1) → (Fin d → ℝ),
        p 0 = u → p (Fin.last L) = v →
        (∀ i, p i ∈ Z) →
        (∀ i : Fin L, p i.castSucc ≠ p i.succ ∧
          IsExposed ℝ Z (segment ℝ (p i.castSucc) (p i.succ))) → r ≤ L := by sorry
