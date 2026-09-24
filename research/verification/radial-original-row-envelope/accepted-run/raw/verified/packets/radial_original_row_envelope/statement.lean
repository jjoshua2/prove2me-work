import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.original_row_radial_max_envelope (d m : ℕ) (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ)) = {x | ∀ i, A i x ≤ b i})
    (v : Fin d → ℝ)
    (hv : v ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ) :
    ∃ h : (Fin d → ℝ) →ₗ[ℝ] ℝ,
      (∀ x ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)),
        x ≠ v → 0 < h (x - v)) ∧
      (∀ (y : Fin d → ℝ) (a : ℝ), 0 < a →
        ((∀ i, A i (v + (1 / a) • y) ≤ b i) ↔
          (∀ i, A i v = b i → A i y ≤ 0) ∧
          (∀ i, A i v < b i → A i y / (b i - A i v) ≤ a))) ∧
      (∀ y : Fin d → ℝ, h y = 1 → (∀ i, A i v = b i → A i y ≤ 0) →
        ∃ i : Fin m, A i v < b i ∧ 0 < A i y / (b i - A i v) ∧
          (∀ j, A j v < b j →
            A j y / (b j - A j v) ≤ A i y / (b i - A i v)) ∧
          ∀ a : ℝ, 0 < a →
            ((∀ j, A j (v + (1 / a) • y) ≤ b j) ↔
              A i y / (b i - A i v) ≤ a)) ∧
      (∀ x ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ,
        x ≠ v →
        let y := (1 / h (x - v)) • (x - v)
        let a := 1 / h (x - v)
        h y = 1 ∧ v + (1 / a) • y = x ∧
          (∀ i, A i x = b i ↔ A i y = a * (b i - A i v)) ∧
          (∀ i, A i v < b i → A i y / (b i - A i v) ≤ a) ∧
          ∃ i, A i v < b i ∧ A i y / (b i - A i v) = a) ∧
      (∀ u w : Fin d → ℝ,
        u ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ →
        w ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ →
        u ≠ v → w ≠ v → u ≠ w →
        IsExposed ℝ {x : Fin d → ℝ | ∀ i, A i x ≤ b i} (segment ℝ u w) →
        ∃ i : Fin m, A i v < b i ∧ A i u = b i ∧ A i w = b i) ∧
      Set.InjOn (fun x => (1 / h (x - v)) • (x - v))
        (({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ \ {v}) := by sorry
