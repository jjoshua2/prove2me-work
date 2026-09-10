import Definitions.Def_Hirsch_circuit_model

set_option autoImplicit false
open scoped RealInnerProductSpace

/-- OPEN RESEARCH CLAIM, not a consequence of the circuit-diameter paper.
Only irredundant, strictly feasible presentations are considered. An entire
circuit walk between vertices may be replaced by an edge walk with polynomial
overhead. It is NOT required to visit nonvertex circuit intermediates.
The essential polynomial-Hirsch difficulty remains in this claim. -/
theorem Hirsch.polynomial_edge_refinement_of_circuit_walks :
    ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hirsch.Hpoly a b) →
      Hirsch.RowPresentationIrredundant a b → Hirsch.StrictlyFeasibleRows a b →
      ∀ u ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      ∀ v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      ∀ L : ℕ, Hirsch.RowCircuitWalk a b L u v →
        ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
          w 0 = u ∧ w (C * (n + d) ^ k * L) = v ∧
          ∀ j < C * (n + d) ^ k * L,
            w j = w (j + 1) ∨
              Hirsch.Adj (Hirsch.Hpoly a b) (w j) (w (j + 1)) := by sorry
