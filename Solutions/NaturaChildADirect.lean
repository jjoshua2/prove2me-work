import Solutions.CircuitPhaseRoute

set_option autoImplicit false
open scoped RealInnerProductSpace

/-- Exact direct solution candidate for Prove2Me theorem
`Hirsch.cubic_circuit_walk_bound` (9b9a6f06-d05d-41ba-980f-04b905e67562),
using the independently kernel-checked explicit standard-slice cubic route. -/
theorem solution :
    ∃ C : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hirsch.Hpoly a b) →
      ∀ u ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      ∀ v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      (∀ j, a j ≠ 0 → ⟪a j, u⟫ ≠ b j ∨ ⟪a j, v⟫ ≠ b j) →
      ∃ m : ℕ, m ≤ n ∧ ∃ e : Fin m ↪ Fin n,
        Hirsch.Hpoly (fun j => a (e j)) (fun j => b (e j)) = Hirsch.Hpoly a b ∧
        Hirsch.RowPresentationIrredundant (fun j => a (e j)) (fun j => b (e j)) ∧
        Hirsch.StrictlyFeasibleRows (fun j => a (e j)) (fun j => b (e j)) ∧
        Hirsch.RowCircuitWalk (fun j => a (e j)) (fun j => b (e j))
          (C * (m + d) ^ 3) u v := by
  exact HirschCircuit.cubic_circuit_walk_bound_of_standard
    HirschCircuit.standard_cubic_circuit_bound

#print axioms solution
