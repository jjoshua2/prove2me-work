import Mathlib
import Solutions.PolynomialCircuitSaturatedBlocker
import Solutions.CircuitPhaseBlockerPersistence

open scoped BigOperators RealInnerProductSpace
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- A saturated selected presentation for a maximal row-circuit step that stays
inside one slack-routing phase has a selected blocker with a precise ordered
interpretation: it is tight only at the step destination, strictly slack at the
fixed final target, and its positive target-slack coordinate was already trapped
at the phase reference.

This bridges the static saturation identity to the actual support-safe cubic
routing order. It is not yet a bound on how often such a blocker can recur. -/
theorem rowCircuitStep_saturated_same_phase_selected_target_positive_blocker
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hstep : RowCircuitStep a b x y)
    (hv : v ∈ Hpoly a b)
    (F : Finset (Fin n))
    (hF : F ⊆ effectiveRowsOnSubspace a (commonDirection a b x y))
    (hface : commonFaceDim a b x y ≤ F.card)
    (hsat :
      (F.card - commonFaceDim a b x y) +
        ((commonFaceDim a b x y - 1) -
          Module.finrank ℝ
            (((rowEvalMap a (F ∩ circuitNeutralRows a (y - x))).domRestrict
              (commonDirection a b x y)).range)) = n - d)
    (M : ℝ) (hM : 0 ≤ M) (r : Fin n → ℝ)
    (heqx :
      HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v) r =
        HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v)
          (HirschCircuit.slack a b x))
    (heqy :
      HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v) r =
        HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v)
          (HirschCircuit.slack a b y)) :
    ∃ i : Fin n,
      i ∈ F ∧
      i ∈ targetOnlyRows a b x y ∧
      ⟪a i, v⟫ < b i ∧
      r i ≤ M * HirschCircuit.slack a b v i ∧
      HirschCircuit.slack a b y i = 0 ∧
      HirschCircuit.slack a b y i < HirschCircuit.slack a b x i := by
  obtain ⟨i, hiF, hia, hiy, hipos⟩ :=
    rowCircuitStep_saturated_selected_target_blocker
      a b x y hbd hstep F hF hface hsat
  have hxne : ⟪a i, x⟫ ≠ b i := by
    intro hix
    rw [inner_sub_right, hiy, hix, sub_self] at hipos
    exact (lt_irrefl 0 hipos)
  have hiTargetOnly : i ∈ targetOnlyRows a b x y := by
    simp [targetOnlyRows, hia, hxne, hiy]
  have hsy : HirschCircuit.slack a b y i = 0 := by
    simp [HirschCircuit.slack, hiy]
  have hsxpos : 0 < HirschCircuit.slack a b x i := by
    rw [inner_sub_right, hiy] at hipos
    simpa [HirschCircuit.slack] using hipos
  have hdown :
      HirschCircuit.slack a b y i < HirschCircuit.slack a b x i := by
    rw [hsy]
    exact hsxpos
  have hsvnonneg : ∀ j, 0 ≤ HirschCircuit.slack a b v j := by
    intro j
    change 0 ≤ b j - ⟪a j, v⟫
    exact sub_nonneg.mpr (hv j)
  obtain ⟨hsvne, htrap⟩ :=
    HirschCircuit.same_phase_zero_blocker_is_trapped_positive
      M (HirschCircuit.slack a b v) r
        (HirschCircuit.slack a b x) (HirschCircuit.slack a b y)
      hM hsvnonneg heqx heqy i hsy hdown
  have hsvpos : 0 < HirschCircuit.slack a b v i :=
    lt_of_le_of_ne (hsvnonneg i) (Ne.symm hsvne)
  have hvstrict : ⟪a i, v⟫ < b i := by
    change 0 < b i - ⟪a i, v⟫ at hsvpos
    exact sub_pos.mp hsvpos
  exact ⟨i, hiF, hiTargetOnly, hvstrict, htrap, hsy, hdown⟩

#print axioms rowCircuitStep_saturated_same_phase_selected_target_positive_blocker

end HirschCircuitLocalization
