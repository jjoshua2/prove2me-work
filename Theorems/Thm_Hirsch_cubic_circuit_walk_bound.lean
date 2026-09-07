import Definitions.Def_Hirsch_circuit_model

set_option autoImplicit false
open scoped RealInnerProductSpace

/-- Formalization target, NOT a proved local theorem.
Bento Natura, arXiv:2602.06958v2, Theorem 3.1 and Corollary 3.2, after an
injective slack-coordinate identification. The cubic envelope is deliberately
weaker than the paper's O(r^2 log r) bound. These are circuit, not edge, steps. -/
theorem Hirsch.cubic_circuit_walk_bound :
    ∃ C : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hirsch.Hpoly a b) →
      ∀ u ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      ∀ v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
        Hirsch.RowCircuitWalk a b (C * (n + d) ^ 3) u v := by sorry
