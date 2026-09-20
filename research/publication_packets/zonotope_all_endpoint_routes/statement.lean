import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.zonotope_all_endpoint_original_routes (d m : ℕ) (w : Fin m → (Fin d → ℝ))
    (u v : Fin d → ℝ) :
    let Z : Set (Fin d → ℝ) := {x | ∃ s : Fin m → ℝ,
      (∀ i, 0 ≤ s i ∧ s i ≤ 1) ∧ (∑ i : Fin m, s i • w i) = x}
    u ∈ Z.extremePoints ℝ → v ∈ Z.extremePoints ℝ →
      ∃ L : ℕ, L ≤ m ∧ ∃ p : Fin (L+1) → (Fin d → ℝ),
        p 0 = u ∧ p (Fin.last L) = v ∧ (∀ i, p i ∈ Z.extremePoints ℝ) ∧
        ∀ i : Fin L, p i.castSucc ≠ p i.succ ∧
          IsExposed ℝ Z (segment ℝ (p i.castSucc) (p i.succ)) ∧
          IsExtreme ℝ Z (segment ℝ (p i.castSucc) (p i.succ)) := by sorry
