import Mathlib
import Solutions.PolynomialCircuitStepProgress
import Solutions.PolynomialCircuitInjectiveCheckpointLocalization

open scoped RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- Maximality removes the target-nullity term from checkpoint localization in
any injective finite row presentation, even when the H-polyhedron is unbounded.
No ambient reference vertex is needed.

For a maximal row-circuit step `x -> y`:

`commonFaceDim(x,y) + d ≤ n + commonFaceDim(x,x)`. -/
theorem rowCircuitStep_commonFaceDim_source_bound_of_injective
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (hstep : RowCircuitStep a b x y) :
    commonFaceDim a b x y + d ≤ n + commonFaceDim a b x x := by
  have hloc := rowCircuit_commonFaceDim_checkpoint_localization_of_injective
    a b x y hinj hstep.2.2.1
  have hdrop := rowCircuitStep_target_commonFaceDim_lt a b x y hstep
  omega

/-- Equivalent strict progress form on an injective presentation:

`commonFaceDim(y,y) + d + 1 ≤ n + commonFaceDim(x,x)`.

Thus the exact maximal-step carrier/source-self-face inequality used by the
bounded parent survives in pointed unbounded deletion outers. -/
theorem rowCircuitStep_target_commonFaceDim_progress_of_injective
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (hstep : RowCircuitStep a b x y) :
    commonFaceDim a b y y + d + 1 ≤ n + commonFaceDim a b x x := by
  have hcarrier := rowCircuitStep_commonFaceDim_source_bound_of_injective
    a b x y hinj hstep
  have hdrop := rowCircuitStep_target_commonFaceDim_lt a b x y hstep
  omega

#print axioms rowCircuitStep_commonFaceDim_source_bound_of_injective
#print axioms rowCircuitStep_target_commonFaceDim_progress_of_injective

end HirschCircuitLocalization
