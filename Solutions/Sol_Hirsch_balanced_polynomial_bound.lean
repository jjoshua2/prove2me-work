import Theorems.Thm_Hirsch_polynomial_target_face_access
import Theorems.Thm_Hirsch_diameter_bound_of_target_face_access

open scoped RealInnerProductSpace
open Hirsch

/-- Conditional sketch: the target-face access estimate remains open. -/
theorem solution :
    ∃ C k : ℕ, ∀ (D : ℕ) (a : Fin (2 * D) → EuclideanSpace ℝ (Fin D)) (b : Fin (2 * D) → ℝ),
      (Hpoly a b).Nonempty → Bornology.IsBounded (Hpoly a b) →
      DiamLE (Hpoly a b) (C * D ^ k) := by
  obtain ⟨C, k, haccess⟩ := polynomial_target_face_access
  refine ⟨C * 3 ^ k, k + 1, ?_⟩
  intro D a b _hne hbd
  have hdiam := diameter_bound_of_target_face_access C k haccess D (2 * D) a b hbd
  have hbudget : D * C * (2 * D + D) ^ k = (C * 3 ^ k) * D ^ (k + 1) := by
    rw [show 2 * D + D = 3 * D by omega, mul_pow, pow_succ]
    ring
  simpa only [hbudget] using hdiam
