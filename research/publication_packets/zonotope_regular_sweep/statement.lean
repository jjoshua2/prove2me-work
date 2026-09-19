import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.zonotope_regular_sweep_original_edges (d m : ℕ) (w : Fin m → (Fin d → ℝ))
    (f g : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hf : ∀ i, w i ≠ 0 → f (w i) ≠ 0)
    (hg : ∀ i, w i ≠ 0 → g (w i) ≠ 0) :
    let Z : Set (Fin d → ℝ) := {x | ∃ s : Fin m → ℝ,
      (∀ i, 0 ≤ s i ∧ s i ≤ 1) ∧ (∑ i : Fin m, s i • w i)=x}
    let F : ((Fin d → ℝ) →ₗ[ℝ] ℝ) → Set (Fin d → ℝ) :=
      fun h => {x | x ∈ Z ∧ h x = ∑ i : Fin m, max 0 (h (w i))}
    ∃ k : (Fin d → ℝ) →ₗ[ℝ] ℝ, ∃ T : Finset ℝ,
      (∀ i, (0 < k (w i) ↔ 0 < g (w i)) ∧ (w i ≠ 0 → k (w i) ≠ 0)) ∧
      F k = F g ∧ T.card ≤ m ∧
      (∀ t, t ∈ T ↔ 0 < t ∧ t < 1 ∧
        ∃ i, w i ≠ 0 ∧ ((1-t) • f + t • k) (w i)=0) ∧
      (∀ t ∈ T, ∃ u v : Fin d → ℝ, u ≠ v ∧ F ((1-t) • f + t • k)=segment ℝ u v ∧
        IsExposed ℝ Z (segment ℝ u v) ∧ IsExtreme ℝ Z (segment ℝ u v) ∧
        u ∈ Z.extremePoints ℝ ∧ v ∈ Z.extremePoints ℝ) ∧
      (∀ t, 0 ≤ t → t ≤ 1 → t ∉ T →
        ∃ u ∈ Z.extremePoints ℝ, F ((1-t) • f + t • k)={u}) := by sorry
