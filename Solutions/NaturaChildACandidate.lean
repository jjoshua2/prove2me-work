import Solutions.CircuitFiniteRouting

set_option autoImplicit false
open scoped RealInnerProductSpace

/-! UNCOMPILED CANDIDATE for Prove2Me theorem
Hirsch.cubic_circuit_walk_bound, id 9b9a6f06-d05d-41ba-980f-04b905e67562.
The result type is copied from the checked conditional source bridge at
integration commit a24d31a77362801e9f6f9ff3530d0ba97c803e7a.
Do not submit this file until the complete new dependency chain compiles and
the axiom audit succeeds. Prove2Me deployment must flatten local Solutions
imports or publish their reusable dependencies through the normal APIs. -/

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
    HirschCircuit.standardCubicCircuitBound_explicit

#print axioms solution
