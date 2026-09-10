import Solutions.PolynomialCircuitLocalizationBalanced
import Definitions.Def_Hirsch_circuit_slack_model

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

/-- Public adapter for the balanced/estranged obstruction. -/
theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbal : n = 2 * d) (hd : 2 ≤ d)
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u)) :
    ∃ i : Fin n, a i ≠ 0 ∧ ⟪a i, u⟫ = b i ∧ ⟪a i, v⟫ = b i := by
  exact HirschCircuitLocalization.balanced_rowCircuit_vertices_share_nonzero_tight_row
    a b u v hbal hd hu hv hcirc

#print axioms solution
