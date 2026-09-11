import Mathlib
import Definitions.Def_Hirsch_circuit_model
import Solutions.PolynomialCircuitCarrierRouting
import Solutions.PolynomialCommonFaceExcessTwoCarrier

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- Finite H-polyhedra are closed. -/
lemma hpoly_isClosed {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    IsClosed (Hpoly a b) := by
  rw [show Hpoly a b = ⋂ i : Fin n,
      {x : EuclideanSpace ℝ (Fin d) | ⟪a i, x⟫ ≤ b i} by
    ext x
    simp [Hpoly]]
  exact isClosed_iInter (fun i =>
    isClosed_le (continuous_const.inner continuous_id) continuous_const)

/-- In ambient row excess at most two, any feasible checkpoint sequence with
vertex endpoints admits a parent graph route paying at most two edges per old
step. The old sequence need not itself be a circuit walk and its interior
checkpoints need not be vertices. -/
theorem feasible_sequence_edge_route_two_mul_of_rows_le_dim_add_two
    (hsmall : SmallExcessHpolyBound)
    {d n L : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hrows : n ≤ d + 2)
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hfeas : ∀ k ≤ L, w k ∈ Hpoly a b)
    (h0 : w 0 ∈ extremePoints ℝ (Hpoly a b))
    (hL : w L ∈ extremePoints ℝ (Hpoly a b)) :
    HirschRegionRoute.Route (Adj (Hpoly a b)) (2 * L) (w 0) (w L) := by
  have hP : IsCompact (Hpoly a b) :=
    Metric.isCompact_iff_isClosed_bounded.2 ⟨hpoly_isClosed a b, hbd⟩
  let B : Fin L → ℕ := fun _ => 2
  have hB : ∀ i : Fin L,
      DiamLE (commonFace a b (w i.val) (w (i.val + 1))) (B i) := by
    intro i
    simpa [B] using
      commonFace_diamLE_two_of_rows_le_dim_add_two hsmall a b
        (w i.val) (w (i.val + 1)) hbd
        (hfeas i.val (Nat.le_of_lt i.isLt)) hrows
  have hroute := route_of_feasible_commonFace_carrier_budgets
    a b hP w L hfeas h0 hL B hB
  simpa [B, Nat.mul_comm] using hroute

/-- Every padded row-circuit walk in ambient row excess at most two can be
refined to an ordinary edge/stay walk with at most two graph steps per circuit
step. Intermediate circuit checkpoints may be nonvertices. -/
theorem rowCircuitWalk_edge_route_two_mul_of_rows_le_dim_add_two
    (hsmall : SmallExcessHpolyBound)
    {d n L : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hrows : n ≤ d + 2)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hcw : RowCircuitWalk a b L u v) :
    HirschRegionRoute.Route (Adj (Hpoly a b)) (2 * L) u v := by
  obtain ⟨w, hw0, hwL, hfeas, _hsteps⟩ := hcw
  have h0 : w 0 ∈ extremePoints ℝ (Hpoly a b) := by simpa [hw0] using hu
  have hL : w L ∈ extremePoints ℝ (Hpoly a b) := by simpa [hwL] using hv
  have hroute := feasible_sequence_edge_route_two_mul_of_rows_le_dim_add_two
    hsmall a b hbd hrows w hfeas h0 hL
  simpa [hw0, hwL] using hroute

#print axioms hpoly_isClosed
#print axioms feasible_sequence_edge_route_two_mul_of_rows_le_dim_add_two
#print axioms rowCircuitWalk_edge_route_two_mul_of_rows_le_dim_add_two

end HirschCircuitLocalization
