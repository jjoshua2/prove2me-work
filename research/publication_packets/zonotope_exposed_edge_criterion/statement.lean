import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.zonotope_exposed_edge_iff_tied_collinear (d m : ℕ) (w : Fin m → (Fin d → ℝ))
    (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) :
    let Z : Set (Fin d → ℝ) := {x | ∃ t : Fin m → ℝ,
      (∀ i, 0 ≤ t i ∧ t i ≤ 1) ∧ (∑ i : Fin m, t i • w i)=x}
    let F : Set (Fin d → ℝ) := {x | x ∈ Z ∧ f x = ∑ i : Fin m, max 0 (f (w i))}
    (∃ u v : Fin d → ℝ, u ≠ v ∧ F=segment ℝ u v ∧
      IsExposed ℝ Z (segment ℝ u v) ∧ IsExtreme ℝ Z (segment ℝ u v) ∧
      u ∈ Z.extremePoints ℝ ∧ v ∈ Z.extremePoints ℝ) ↔
    ∃ j : Fin m, w j ≠ 0 ∧ f (w j)=0 ∧
      ∀ i, f (w i)=0 → ∃ c : ℝ, w i=c • w j := by sorry
