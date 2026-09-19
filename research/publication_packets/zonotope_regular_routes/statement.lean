import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.zonotope_regular_objective_original_routes (d m : ℕ) (w : Fin m → (Fin d → ℝ))
    (f g : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hf : ∀ i, w i ≠ 0 → f (w i) ≠ 0)
    (hg : ∀ i, w i ≠ 0 → g (w i) ≠ 0) :
    let Z : Set (Fin d → ℝ) := {x | ∃ s : Fin m → ℝ,
      (∀ i, 0 ≤ s i ∧ s i ≤ 1) ∧ (∑ i : Fin m, s i • w i)=x}
    let F : ((Fin d → ℝ) →ₗ[ℝ] ℝ) → Set (Fin d → ℝ) :=
      fun h => {x | x ∈ Z ∧ h x = ∑ i : Fin m, max 0 (h (w i))}
    ∃ L : ℕ, L ≤ m ∧ ∃ p : Fin (L+1) → (Fin d → ℝ),
      F f = {p 0} ∧ F g = {p (Fin.last L)} ∧
      (∀ i, p i ∈ Z.extremePoints ℝ) ∧
      ∀ i : Fin L, p i.castSucc ≠ p i.succ ∧
        IsExposed ℝ Z (segment ℝ (p i.castSucc) (p i.succ)) ∧
        IsExtreme ℝ Z (segment ℝ (p i.castSucc) (p i.succ)) := by sorry
