import Definitions.Def_Hirsch_circuit_model
import Solutions.PolynomialCircuitCarrierRouting
import Solutions.PolynomialCommonFaceExcessTwoCarrier

/-!
# Two ordinary graph steps per feasible checkpoint in ambient row excess two

This composes two already-verified ingredients:

* feasible nonvertex checkpoint sequences can be rounded and routed through
  their consecutive intrinsic common carriers; and
* in a bounded H-presentation with `n ≤ d+2`, every such carrier based at a
  feasible checkpoint has intrinsic padded diameter at most two.

The circuit structure of the checkpoint sequence is not used.  Consequently
any feasible sequence with vertex endpoints admits the same `2L` graph route.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace HirschPolynomialAccess

/-- A length-`L` feasible checkpoint sequence in a compact `n ≤ d+2`
H-polytope, with vertex endpoints, has an ordinary edge/stay route of length
`2L`. Intermediate checkpoints need not be vertices and the output route need
not visit them. -/
theorem route_of_feasible_sequence_two_per_step_of_rows_le_dim_add_two
    {d n : ℕ}
    (hsmall : HirschCircuitLocalization.SmallExcessHpolyBound)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hP : IsCompact (Hpoly a b))
    (hrows : n ≤ d + 2)
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hfeas : ∀ k ≤ L, w k ∈ Hpoly a b)
    (h0 : w 0 ∈ extremePoints ℝ (Hpoly a b))
    (hL : w L ∈ extremePoints ℝ (Hpoly a b)) :
    HirschRegionRoute.Route (Adj (Hpoly a b)) (2 * L) (w 0) (w L) := by
  have hcarrier : ∀ i : Fin L,
      DiamLE (commonFace a b (w i.val) (w (i.val + 1))) 2 := by
    intro i
    exact HirschCircuitLocalization.commonFace_diamLE_two_of_rows_le_dim_add_two
      hsmall a b (w i.val) (w (i.val + 1)) hP.isBounded
      (hfeas i.val (by omega)) hrows
  have hroute := route_of_feasible_commonFace_carrier_budgets
    a b hP w L hfeas h0 hL (fun _ : Fin L => 2) hcarrier
  simpa [Nat.mul_comm] using hroute

/-- A row-circuit walk is in particular a feasible checkpoint sequence. Hence,
in ambient row excess at most two, a length-`L` circuit walk between parent
vertices admits a `2L` ordinary edge/stay route. No assumption that its
intermediate circuit checkpoints are vertices is made. -/
theorem edge_route_of_rowCircuitWalk_two_per_step_of_rows_le_dim_add_two
    {d n L : ℕ}
    (hsmall : HirschCircuitLocalization.SmallExcessHpolyBound)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hP : IsCompact (Hpoly a b))
    (hrows : n ≤ d + 2)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hcw : RowCircuitWalk a b L u v) :
    HirschRegionRoute.Route (Adj (Hpoly a b)) (2 * L) u v := by
  obtain ⟨w, hw0, hwL, hfeas, _hsteps⟩ := hcw
  have h0 : w 0 ∈ extremePoints ℝ (Hpoly a b) := by
    rw [hw0]
    exact hu
  have hL : w L ∈ extremePoints ℝ (Hpoly a b) := by
    rw [hwL]
    exact hv
  have hroute := route_of_feasible_sequence_two_per_step_of_rows_le_dim_add_two
    hsmall a b hP hrows w L hfeas h0 hL
  simpa [hw0, hwL] using hroute

#print axioms route_of_feasible_sequence_two_per_step_of_rows_le_dim_add_two
#print axioms edge_route_of_rowCircuitWalk_two_per_step_of_rows_le_dim_add_two

end HirschPolynomialAccess
