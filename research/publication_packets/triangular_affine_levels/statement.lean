import Mathlib
set_option autoImplicit false

theorem Hirsch.triangular_extreme_points_force_exponential_affine_levels (e : ℝ) (he : 0 < e) (he2 : e < 1/2) (n : ℕ) :
    ∃ V : Finset (Fin (n+1) → ℝ), V.card = 2^(n+1) ∧
      (∀ x ∈ V, x ∈
        ({y : Fin (n+1) → ℝ |
          (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧
          ∀ (i j : Fin (n+1)), i.val+1 = j.val → e*y j ≤ y i ∧ y i ≤ 1-e*y j}).extremePoints ℝ) ∧
      ∀ (r : ℕ) (T : (Fin (n+1) → ℝ) →ₗ[ℝ] (Fin r → ℝ)),
        Function.Injective T → ∀ offset : Fin r → ℝ,
          ∃ j : Fin r, 2^(n+1) ≤
            (V.image (fun x => (T x) j + offset j)).card *
              ((V.image (fun x => (T x) j + offset j)).card - 1) := by sorry
