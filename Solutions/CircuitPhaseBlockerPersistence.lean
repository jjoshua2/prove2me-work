import Mathlib
import Solutions.CircuitSourceBridge
import Solutions.CircuitAugmentation
import Solutions.CircuitPhaseProgress

set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators
open Hirsch

namespace HirschCircuit

/-- The affine part of the standard nonnegative slice is preserved along the
whole line through two feasible points. -/
theorem standardSlice_line_affine_mem {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c x y : Fin n → ℝ)
    (hx : x ∈ StandardSlice K c) (hy : y ∈ StandardSlice K c)
    (t : ℝ) :
    (x + t • (y - x)) - c ∈ K := by
  have hdir : y - x ∈ K := by
    have h := K.sub_mem hy.1 hx.1
    convert h using 1 <;> module
  have hsum := K.add_mem hx.1 (K.smul_mem t hdir)
  convert hsum using 1 <;> module

/-- Every nonstationary maximal circuit step in a nonnegative affine slice is
blocked by a coordinate that moved strictly downward and is zero at the new
checkpoint. -/
theorem standardCircuitStep_exists_zero_blocker {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c x y : Fin n → ℝ)
    (hstep : StandardCircuitStep K c x y) :
    ∃ q : Fin n, y q = 0 ∧ y q < x q := by
  classical
  let g : Fin n → ℝ := y - x
  have hx : x ∈ StandardSlice K c := hstep.1
  have hy : y ∈ StandardSlice K c := hstep.2.1
  have hzero : ∀ i, x i = 0 → 0 ≤ g i := by
    intro i hxi
    dsimp [g]
    change 0 ≤ y i - x i
    rw [hxi, sub_zero]
    exact hy.2 i
  have hneg : ∃ i, g i < 0 := by
    by_contra hn
    push_neg at hn
    have h2 : x + (2 : ℝ) • g ∈ StandardSlice K c := by
      refine ⟨?_, ?_⟩
      · simpa [g] using standardSlice_line_affine_mem K c x y hx hy (2 : ℝ)
      · intro i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact add_nonneg (hx.2 i) (mul_nonneg (by norm_num) (hn i))
    exact (hstep.2.2.2 (2 : ℝ) (by norm_num)) h2
  obtain ⟨α, hα, hfeas, ⟨q, hqneg, hqsat⟩, hmax⟩ :=
    exists_positive_maximal_nonnegative_step x g hx.2 hzero hneg
  have hαle : α ≤ 1 := by
    by_contra hn
    have hlt : 1 < α := lt_of_not_ge hn
    have hαslice : x + α • g ∈ StandardSlice K c := by
      refine ⟨?_, ?_⟩
      · simpa [g] using standardSlice_line_affine_mem K c x y hx hy α
      · intro i
        simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hfeas i
    exact (hstep.2.2.2 α hlt) hαslice
  have h1le : 1 ≤ α := by
    by_contra hn
    have hlt : α < 1 := lt_of_not_ge hn
    obtain ⟨i, hi⟩ := hmax 1 hlt
    have hyi := hy.2 i
    dsimp [g] at hi
    change x i + 1 * (y i - x i) < 0 at hi
    linarith
  have hαeq : α = 1 := le_antisymm hαle h1le
  refine ⟨q, ?_, ?_⟩
  · dsimp [g] at hqsat
    rw [hαeq] at hqsat
    linarith
  · dsimp [g] at hqneg
    linarith

/-- If a current and next checkpoint remain in the same phase, a newly zero
blocking coordinate cannot be target-zero.  It is target-positive and was
already trapped at the phase reference. -/
theorem same_phase_zero_blocker_is_trapped_positive {n : ℕ}
    (M : ℝ) (v r x y : Fin n → ℝ)
    (hM : 0 ≤ M) (hv : ∀ i, 0 ≤ v i)
    (heqx : phaseProgressSet M v r = phaseProgressSet M v x)
    (heqy : phaseProgressSet M v r = phaseProgressSet M v y)
    (q : Fin n) (hyq : y q = 0) (hdown : y q < x q) :
    v q ≠ 0 ∧ r q ≤ M * v q := by
  have htrap := same_phase_reference_trapped_of_current_zero
    M v r y heqy hM hv q hyq
  refine ⟨?_, htrap⟩
  intro hv0
  have hr0 : r q = 0 :=
    (same_phase_zero_iff M v r y heqy q hv0).2 hyq
  have hx0 : x q = 0 :=
    (same_phase_zero_iff M v r x heqx q hv0).1 hr0
  rw [hyq, hx0] at hdown
  exact (lt_irrefl 0 hdown)

/-- Ordered blocker classification for a maximal step that stays inside one
phase: some blocking coordinate is target-positive and was already trapped at
the phase reference.  Thus no-progress bulk steps cannot be blocked by a fresh
target-zero coordinate. -/
theorem standardCircuitStep_same_phase_has_trapped_positive_blocker {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ))
    (M : ℝ) (v r x y : Fin n → ℝ)
    (hM : 0 ≤ M) (hv : ∀ i, 0 ≤ v i)
    (hstep : StandardCircuitStep K v x y)
    (heqx : phaseProgressSet M v r = phaseProgressSet M v x)
    (heqy : phaseProgressSet M v r = phaseProgressSet M v y) :
    ∃ q : Fin n,
      v q ≠ 0 ∧ r q ≤ M * v q ∧ y q = 0 ∧ y q < x q := by
  obtain ⟨q, hyq, hdown⟩ := standardCircuitStep_exists_zero_blocker K v x y hstep
  obtain ⟨hvq, htrap⟩ := same_phase_zero_blocker_is_trapped_positive
    M v r x y hM hv heqx heqy q hyq hdown
  exact ⟨q, hvq, htrap, hyq, hdown⟩

#print axioms standardSlice_line_affine_mem
#print axioms standardCircuitStep_exists_zero_blocker
#print axioms same_phase_zero_blocker_is_trapped_positive
#print axioms standardCircuitStep_same_phase_has_trapped_positive_blocker

end HirschCircuit
