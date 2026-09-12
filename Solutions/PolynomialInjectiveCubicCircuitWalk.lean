import Mathlib
import Solutions.CircuitPhaseRoute

open scoped RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCircuit

/-- The cubic standard-slice construction needs no boundedness assumption once
injectivity of the row-evaluation map is supplied directly.

The source point only needs to be feasible; the target must be a vertex.  This
is the form needed for pointed but potentially unbounded one-row deletion
outers. -/
theorem rowCircuitWalk_explicit_cubic_of_injective
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (rowMap a))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b)
    (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    RowCircuitWalk a b (17 * n ^ 3) u v := by
  have hsu : slack a b u ∈
      StandardSlice (LinearMap.range (rowMap a)) b := by
    rw [← slackPoly_eq_standardSlice a b]
    exact (slack_mem_SlackPoly_iff a b u).mpr hu
  have hsv : slack a b v ∈
      extremePoints ℝ (StandardSlice (LinearMap.range (rowMap a)) b) := by
    have h := slack_mem_extremePoints_of_mem_extremePoints a b hinj v hv
    rwa [slackPoly_eq_standardSlice a b] at h
  have hw := standardCircuitWalk_cubic
    (LinearMap.range (rowMap a)) b
    (slack a b u) (slack a b v) hsu hsv
  apply (rowCircuitWalk_iff_slackCircuitWalk
    a b hinj (17 * n ^ 3) u v).mpr
  exact (slackCircuitWalk_iff_standardCircuitWalk
    a b (17 * n ^ 3) (slack a b u) (slack a b v)).mpr hw

#print axioms rowCircuitWalk_explicit_cubic_of_injective

end HirschCircuit
