import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.cut_vertex_selected_active_square_system
    (m d : ℕ) (S : Set (Fin d → ℝ))
    (C : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (x : Fin d → ℝ)
    (hx : x ∈ (convexHull ℝ S ∩ {y | ∀ j, C j y ≤ b j}).extremePoints ℝ) :
    ∃ (n : ℕ) (v : Fin n → Fin d → ℝ) (w : Fin n → ℝ)
      (J : Finset {j : Fin m // C j x = b j}),
      (∀ i, v i ∈ S) ∧ (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
      (∑ i, w i • v i) = x ∧
      LinearIndependent ℝ (fun i => ((1 : ℝ), v i)) ∧
      n ≤ d + 1 ∧ J.card + 1 = n ∧
      (∀ (mass : ℝ) (values : J → ℝ), ∃! u : Fin n → ℝ,
        (∑ i, u i) = mass ∧
          ∀ j : J, (∑ i, u i * C j.val.val (v i)) = values j) ∧
      (∀ u : Fin n → ℝ, (∑ i, u i) = 1 →
        (∀ j : J, (∑ i, u i * C j.val.val (v i)) = b j.val.val) → u = w) := by sorry
