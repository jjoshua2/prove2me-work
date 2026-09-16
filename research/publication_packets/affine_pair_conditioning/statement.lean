import Mathlib
set_option autoImplicit false

theorem Hirsch.affine_pair_conditioning_optimum (e : ℝ) (he : 0 < e) (he1 : e < 1) :
    (∀ X Y Z : ℝ, 0 < X → 0 < Y → Z ^ 2 < X * Y →
      min (e ^ 2 * (X * Y - Z ^ 2) /
            (X * (X + 2 * e * Z + e ^ 2 * Y)))
          (e ^ 2 * (X * Y - Z ^ 2) /
            (Y * (Y + 2 * e * Z + e ^ 2 * X))) ≤ e ^ 2) ∧
    ∃ X Y Z : ℝ, 0 < X ∧ 0 < Y ∧ Z ^ 2 < X * Y ∧
      min (e ^ 2 * (X * Y - Z ^ 2) /
            (X * (X + 2 * e * Z + e ^ 2 * Y)))
          (e ^ 2 * (X * Y - Z ^ 2) /
            (Y * (Y + 2 * e * Z + e ^ 2 * X))) = e ^ 2 := by sorry
