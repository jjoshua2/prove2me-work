import Mathlib
import Solutions.PolynomialCircuitCheckpointLocalization
import Solutions.PolynomialCircuitInjectiveNeutralRank

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- For an injective row presentation, a row circuit has zero all-neutral
rank defect without needing any reference vertex or boundedness hypothesis. -/
theorem directionNeutralDefect_eq_zero_of_rowCircuit_of_injective
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (g : EuclideanSpace ℝ (Fin d))
    (hg : IsRowCircuit a g) :
    directionNeutralDefect a g = 0 := by
  unfold directionNeutralDefect
  rw [rowCircuit_neutral_rank_eq_dim_sub_one_of_injective a hinj g hg,
    Nat.sub_self]

/-- Sharp nonvertex circuit checkpoint localization for any injective finite
row presentation, bounded or unbounded.

Compared with `rowCircuit_commonFaceDim_checkpoint_localization`, no ambient
reference vertex is required: injectivity supplies the exact neutral rank
directly. -/
theorem rowCircuit_commonFaceDim_checkpoint_localization_of_injective
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (hcirc : IsRowCircuit a (y - x)) :
    2 * commonFaceDim a b x y + d ≤
      n + commonFaceDim a b x x + commonFaceDim a b y y + 1 := by
  have h := commonFaceDim_checkpoint_localization_with_directionDefect a b x y
  rw [directionNeutralDefect_eq_zero_of_rowCircuit_of_injective
    a hinj (y - x) hcirc] at h
  simpa only [Nat.add_zero] using h

#print axioms directionNeutralDefect_eq_zero_of_rowCircuit_of_injective
#print axioms rowCircuit_commonFaceDim_checkpoint_localization_of_injective

end HirschCircuitLocalization
