import Solutions.PolynomialExcessTwoDiameter

open scoped BigOperators RealInnerProductSpace
open Set

/-- The public statement uses only Mathlib primitives. The adjacency condition
is expanded, so its meaning is independent of any local graph definition. -/
theorem solution {n : ℕ} (t : Fin n → ℝ) (mu : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    let P : Set (EuclideanSpace ℝ (Fin n)) :=
      {s | (∀ i, 0 ≤ s i) ∧ (∑ i, s i) = 1 ∧ (∑ i, t i * s i) = mu}
    x ∈ extremePoints ℝ P → y ∈ extremePoints ℝ P →
      ∃ w ∈ extremePoints ℝ P,
        (x = w ∨ (x ≠ w ∧ IsExtreme ℝ P (segment ℝ x w))) ∧
        (w = y ∨ (w ≠ y ∧ IsExtreme ℝ P (segment ℝ w y))) ∧
        ∀ i, x i = 0 → y i = 0 → w i = 0 := by
  dsimp only
  intro hx hy
  exact HirschExcessTwo.momentSlice_two_step_route t mu x y hx hy

#print axioms solution
