import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.planar_original_halfspace_half_bound (m : ℕ) (C : Finset (Fin 2 → ℝ))
    (A : Fin m → (Fin 2 → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin 2 → ℝ)) = {x | ∀ i, A i x ≤ b i})
    (u v : Fin 2 → ℝ)
    (hu : u ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin 2 → ℝ)).extremePoints ℝ)
    (hv : v ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin 2 → ℝ)).extremePoints ℝ) :
    ∃ L : ℕ, 2 * L ≤ m ∧ ∃ q : Fin (L + 1) → (Fin 2 → ℝ),
      q 0 = u ∧ q (Fin.last L) = v ∧
      (∀ i, q i ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin 2 → ℝ)).extremePoints ℝ) ∧
      ∀ i : Fin L, q i.castSucc ≠ q i.succ ∧
        IsExposed ℝ {x : Fin 2 → ℝ | ∀ i, A i x ≤ b i}
          (segment ℝ (q i.castSucc) (q i.succ)) := by sorry
