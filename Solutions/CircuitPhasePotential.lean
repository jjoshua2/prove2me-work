import Solutions.CircuitNormStep
import Solutions.CircuitEliminationParameters

set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped BigOperators

namespace HirschCircuit

/-- Extremality supplies a live target-zero coordinate whenever the current
point differs from the target. The corrected phase invariant ensures its
reference denominator is positive. -/
theorem exists_live_target_zero {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (M : ℝ) (v r x : Fin n → ℝ)
    (hv : v ∈ Set.extremePoints ℝ (StandardSlice K v))
    (hr : r ∈ StandardSlice K v) (hx : x ∈ StandardSlice K v)
    (heq : phaseProgressSet M v r = phaseProgressSet M v x) (hne : x ≠ v) :
    ∃ q, q ∈ liveZeroSet v r ∧ 0 < x q ∧ 0 < r q := by
  classical
  have hex : ∃ q, v q = 0 ∧ x q ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hne (eq_target_of_zero_off_support K v x hv hx hn)
  obtain ⟨q, hvq, hxq⟩ := hex
  have hrq : r q ≠ 0 := by
    intro hrq0
    exact hxq ((same_phase_zero_iff M v r x heq q hvq).mp hrq0)
  refine ⟨q, ?_, ?_, ?_⟩
  · exact (mem_liveZeroSet v r q).mpr ⟨hvq, hrq⟩
  · exact lt_of_le_of_ne (hx.2 q) (Ne.symm hxq)
  · exact lt_of_le_of_ne (hr.2 q) (Ne.symm hrq)

theorem ratio_le_phasePotential {n : ℕ}
    (v r x : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (hx : ∀ i, 0 ≤ x i)
    (q : Fin n) (hq : q ∈ liveZeroSet v r) :
    x q / r q ≤ phasePotential v r x := by
  exact Finset.single_le_sum (fun i _ => div_nonneg (hx i) (hr i)) hq

theorem phasePotential_pos_of_ne_target {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (M : ℝ) (v r x : Fin n → ℝ)
    (hv : v ∈ Set.extremePoints ℝ (StandardSlice K v))
    (hr : r ∈ StandardSlice K v) (hx : x ∈ StandardSlice K v)
    (heq : phaseProgressSet M v r = phaseProgressSet M v x) (hne : x ≠ v) :
    0 < phasePotential v r x := by
  obtain ⟨q, hq, hxq, hrq⟩ := exists_live_target_zero K M v r x hv hr hx heq hne
  exact (div_pos hxq hrq).trans_le (ratio_le_phasePotential v r x hr.2 hx.2 q hq)

/-- Resetting the reference makes every live ratio exactly one. -/
theorem phasePotential_self_le_n {n : ℕ} (v r : Fin n → ℝ) :
    phasePotential v r r ≤ (n : ℝ) := by
  classical
  have hid : phasePotential v r r = ((liveZeroSet v r).card : ℝ) := by
    unfold phasePotential
    calc
      (∑ i ∈ liveZeroSet v r, r i / r i) = ∑ _i ∈ liveZeroSet v r, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact div_self ((mem_liveZeroSet v r i).mp hi).2
      _ = ((liveZeroSet v r).card : ℝ) := by simp
  rw [hid]
  have hcard : (liveZeroSet v r).card ≤ n := by
    simpa using (Finset.card_le_card (Finset.subset_univ (liveZeroSet v r)))
  exact_mod_cast hcard

/-- A small potential supplies all concrete elimination hypotheses; no
unproved progress or maximal-step assumption is passed in. -/
theorem exists_elimination_step_of_small_potential {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (M : ℕ) (hM : 2 ≤ M) (hnM : n ≤ M)
    (v r x : Fin n → ℝ)
    (hv : v ∈ Set.extremePoints ℝ (StandardSlice K v))
    (hr : r ∈ StandardSlice K v) (hx : x ∈ StandardSlice K v)
    (heq : phaseProgressSet (M : ℝ) v r = phaseProgressSet (M : ℝ) v x)
    (hne : x ≠ v) (hsmall : phasePotential v r x ≤ 1 / (2 * (M : ℝ) ^ 2)) :
    ∃ y : Fin n → ℝ, StandardCircuitStep K v x y ∧
      phaseProgressSet (M : ℝ) v x ⊂ phaseProgressSet (M : ℝ) v y := by
  obtain ⟨q, hq, hxq, hrq⟩ := exists_live_target_zero K (M : ℝ) v r x hv hr hx heq hne
  have hvq := ((mem_liveZeroSet v r q).mp hq).1
  have hratio := (ratio_le_phasePotential v r x hr.2 hx.2 q hq).trans hsmall
  obtain ⟨y, hstep, hstrict, _⟩ := exists_elimination_step_of_small_ratio
    K M hM hnM v r x hv.1.2 hr hx heq q hvq hxq hrq hratio
  exact ⟨y, hstep, hstrict⟩

#print axioms phasePotential_pos_of_ne_target
#print axioms phasePotential_self_le_n
#print axioms exists_elimination_step_of_small_potential
end HirschCircuit
