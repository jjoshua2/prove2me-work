import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.moment_all_endpoint_linear_original_routes (d m : ℕ) (hm : d < m) (a : Fin m → ℝ) (ha : StrictMono a)
    (u v : Fin d → ℝ) :
    let row : (Fin d → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin d, (a i ^ (j.val+1) - (∑ z, a z ^ (j.val+1)) / (m : ℝ)) * x j
    let P : Set (Fin d → ℝ) := {x | ∀ i, row x i ≤ 1}
    u ∈ P.extremePoints ℝ → v ∈ P.extremePoints ℝ →
      ∃ L : ℕ, L ≤ 2 * (m-d) + 1 ∧ ∃ p : ℕ → (Fin d → ℝ),
        p 0 = u ∧ p L = v ∧ (∀ t, t ≤ L → p t ∈ P.extremePoints ℝ) ∧
        ∀ t, t < L → p t ≠ p (t+1) ∧
          IsExposed ℝ P (segment ℝ (p t) (p (t+1))) ∧
          IsExtreme ℝ P (segment ℝ (p t) (p (t+1))) ∧
          {z | z ∈ P ∧ ∀ i, row (p t) i = 1 → row (p (t+1)) i = 1 → row z i = 1} =
            segment ℝ (p t) (p (t+1)) := by sorry
