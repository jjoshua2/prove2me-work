import Solutions.PolynomialCircuitStepBlockerCharacterization
import Definitions.Def_Hirsch_circuit_model

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

/-- Public adapter for the exact tight-row certificate controlling whether two
maximal row-circuit steps can be swapped while preserving both displacements. -/
theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y z : EuclideanSpace ℝ (Fin d))
    (hxy : RowCircuitStep a b x y) (hyz : RowCircuitStep a b y z) :
    let w := x + (z - y)
    (RowCircuitStep a b x w ∧ RowCircuitStep a b w z) ↔
      w ∈ Hpoly a b ∧
      (∃ i : Fin n, a i ≠ 0 ∧ ⟪a i, w⟫ = b i ∧ 0 < ⟪a i, z - y⟫) ∧
      (∃ j : Fin n, a j ≠ 0 ∧ ⟪a j, z⟫ = b j ∧ 0 < ⟪a j, y - x⟫) := by
  exact HirschCircuit.rowCircuitStep_swap_iff_feasible_and_tight_blockers
    a b x y z hxy hyz

#print axioms solution
