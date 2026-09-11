import Solutions.PolynomialExcessTwoVertexClassification

open scoped BigOperators RealInnerProductSpace
open Set

/-- Every feasible point has a vertex representative preserving all its zero
coordinates; the statement contains no locally defined predicates. -/
theorem solution {n : ℕ} (t : Fin n → ℝ) (mu : ℝ)
    (s : EuclideanSpace ℝ (Fin n)) :
    let P : Set (EuclideanSpace ℝ (Fin n)) :=
      {z | (∀ i, 0 ≤ z i) ∧ (∑ i, z i) = 1 ∧ (∑ i, t i * z i) = mu}
    s ∈ P → ∃ p ∈ extremePoints ℝ P, ∀ i, s i = 0 → p i = 0 := by
  dsimp only
  intro hs
  exact HirschExcessTwo.exists_extremePoint_preserving_zeros t mu s hs

#print axioms solution
