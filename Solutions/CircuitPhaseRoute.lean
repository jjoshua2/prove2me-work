import Solutions.CircuitPhasePotential
import Solutions.CircuitStandardWalkOps
import Solutions.CircuitContractionBudget
import Solutions.CircuitStandardRecenter

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace HirschCircuit

private theorem walk_end_mem {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c : Fin n → ℝ)
    {L : ℕ} {u x : Fin n → ℝ} (h : StandardCircuitWalk K c L u x) :
    x ∈ StandardSlice K c := by
  obtain ⟨w, _, hwL, hf, _⟩ := h
  simpa only [hwL] using hf L (le_rfl)

/-- Run norm steps only while the fixed-reference phase has not ended.
After an event or arrival, pad at that endpoint. Otherwise the potential
contracts geometrically and the reference/current progress sets stay equal. -/
theorem norm_steps_or_phase_progress {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (M : ℕ) (hM : 2 ≤ M) (hnM : n ≤ M)
    (v r : Fin n → ℝ)
    (hv : v ∈ Set.extremePoints ℝ (StandardSlice K v))
    (hr : r ∈ StandardSlice K v) (k : ℕ) :
    ∃ x : Fin n → ℝ, StandardCircuitWalk K v k r x ∧
      (x = v ∨ phaseProgressSet (M : ℝ) v r ⊂ phaseProgressSet (M : ℝ) v x ∨
        (phaseProgressSet (M : ℝ) v r = phaseProgressSet (M : ℝ) v x ∧
          phasePotential v r x ≤ (1 - 1 / (M : ℝ)) ^ k * phasePotential v r r)) := by
  have hMpos : 0 < M := by omega
  have hMr : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMrpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hq0 : 0 ≤ 1 - 1 / (M : ℝ) := by
    have hdiv : 1 / (M : ℝ) ≤ 1 := (div_le_one hMrpos).mpr (by linarith)
    linarith
  induction k with
  | zero =>
      refine ⟨r, standardCircuitWalk_stationary K v r hr 0, Or.inr (Or.inr ⟨rfl, ?_⟩)⟩
      simp
  | succ k ih =>
      obtain ⟨x, hwalk, hstate⟩ := ih
      rcases hstate with htarget | hstrict | ⟨heq, hbound⟩
      · exact ⟨x, standardCircuitWalk_mono K v hwalk (Nat.le_succ k), Or.inl htarget⟩
      · exact ⟨x, standardCircuitWalk_mono K v hwalk (Nat.le_succ k), Or.inr (Or.inl hstrict)⟩
      · by_cases hxv : x = v
        · exact ⟨x, standardCircuitWalk_mono K v hwalk (Nat.le_succ k), Or.inl hxv⟩
        · have hx := walk_end_mem K v hwalk
          have hW := phasePotential_pos_of_ne_target K (M : ℝ) v r x hv hr hx heq hxv
          obtain ⟨y, g, alpha, ha, ha1, haM, hstep, hyform, hWy, hcontract, hmono, hN⟩ :=
            exists_norm_reduction_step K M hMpos hnM v r x hv.1.2 hr.2 hx hW
          have hcat : StandardCircuitWalk K v (k + 1) r y :=
            standardCircuitWalk_trans K v hwalk (standardCircuitWalk_of_step K v x y hstep)
          have hmono' : phaseProgressSet (M : ℝ) v r ⊆ phaseProgressSet (M : ℝ) v y := by
            rw [heq]
            exact hmono
          refine ⟨y, hcat, Or.inr ?_⟩
          by_cases heq' : phaseProgressSet (M : ℝ) v r = phaseProgressSet (M : ℝ) v y
          · right
            refine ⟨heq', ?_⟩
            calc
              phasePotential v r y ≤ (1 - 1 / (M : ℝ)) * phasePotential v r x := hcontract
              _ ≤ (1 - 1 / (M : ℝ)) *
                  ((1 - 1 / (M : ℝ)) ^ k * phasePotential v r r) :=
                mul_le_mul_of_nonneg_left hbound hq0
              _ = (1 - 1 / (M : ℝ)) ^ (k + 1) * phasePotential v r r := by
                rw [pow_succ]
                ring
          · exact Or.inl (ssubset_of_ne_of_subset heq' hmono')

/-- Every phase reaches the target or strictly enlarges the finite progress
set in at most `4*M^2+1` actual/padded steps. Reference resets are permitted
only after this conclusion, so lost target-zero support is never forgotten. -/
theorem exists_bounded_progress_phase {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (M : ℕ) (hM : 2 ≤ M) (hnM : n ≤ M)
    (v r : Fin n → ℝ)
    (hv : v ∈ Set.extremePoints ℝ (StandardSlice K v))
    (hr : r ∈ StandardSlice K v) :
    ∃ y : Fin n → ℝ, StandardCircuitWalk K v (4 * M ^ 2 + 1) r y ∧
      (y = v ∨ phaseProgressSet (M : ℝ) v r ⊂ phaseProgressSet (M : ℝ) v y) := by
  obtain ⟨x, hwalk, hstate⟩ := norm_steps_or_phase_progress K M hM hnM v r hv hr (4 * M ^ 2)
  rcases hstate with htarget | hstrict | ⟨heq, hbound⟩
  · exact ⟨x, standardCircuitWalk_mono K v hwalk (by omega), Or.inl htarget⟩
  · exact ⟨x, standardCircuitWalk_mono K v hwalk (by omega), Or.inr hstrict⟩
  · by_cases hxv : x = v
    · exact ⟨x, standardCircuitWalk_mono K v hwalk (by omega), Or.inl hxv⟩
    · have hx := walk_end_mem K v hwalk
      have hMr : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      have hMrpos : (0 : ℝ) < (M : ℝ) := by linarith
      have hq0 : 0 ≤ 1 - 1 / (M : ℝ) := by
        have hdiv : 1 / (M : ℝ) ≤ 1 := (div_le_one hMrpos).mpr (by linarith)
        linarith
      have hstart : phasePotential v r r ≤ (M : ℝ) :=
        (phasePotential_self_le_n v r).trans (by exact_mod_cast hnM)
      have hsmall : phasePotential v r x ≤ 1 / (2 * (M : ℝ) ^ 2) := by
        calc
          phasePotential v r x ≤ (1 - 1 / (M : ℝ)) ^ (4 * M ^ 2) * phasePotential v r r := hbound
          _ ≤ (1 - 1 / (M : ℝ)) ^ (4 * M ^ 2) * (M : ℝ) :=
            mul_le_mul_of_nonneg_left hstart (pow_nonneg hq0 _)
          _ = (M : ℝ) * (1 - 1 / (M : ℝ)) ^ (4 * M ^ 2) := mul_comm _ _
          _ ≤ 1 / (2 * (M : ℝ) ^ 2) := contraction_to_elimination_threshold M hM
      obtain ⟨y, hstep, hstrict⟩ := exists_elimination_step_of_small_potential
        K M hM hnM v r x hv hr hx heq hxv hsmall
      refine ⟨y, standardCircuitWalk_trans K v hwalk
        (standardCircuitWalk_of_step K v x y hstep), Or.inr ?_⟩
      rw [heq]
      exact hstrict

/-- Induction on the remaining progress budget assembles all phases. -/
theorem standardCircuitWalk_phase_budget {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (M : ℕ) (hM : 2 ≤ M) (hnM : n ≤ M)
    (v : Fin n → ℝ) (hv : v ∈ Set.extremePoints ℝ (StandardSlice K v)) :
    ∀ k : ℕ, ∀ r ∈ StandardSlice K v,
      n ≤ (phaseProgressSet (M : ℝ) v r).card + k →
      StandardCircuitWalk K v (k * (4 * M ^ 2 + 1)) r v := by
  intro k
  induction k with
  | zero =>
      intro r hr hk
      have hfull : phaseProgressSet (M : ℝ) v r = Finset.univ := by
        apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        simpa only [Finset.card_univ, Fintype.card_fin, Nat.add_zero] using hk
      have hrv := eq_target_of_full_phase_progress K (M : ℝ) v r hv hr hfull
      subst r
      exact standardCircuitWalk_stationary K v v hv.1 _
  | succ k ih =>
      intro r hr hk
      obtain ⟨y, hwalk, hy⟩ := exists_bounded_progress_phase K M hM hnM v r hv hr
      rcases hy with htarget | hstrict
      · rw [htarget] at hwalk
        apply standardCircuitWalk_mono K v hwalk
        nlinarith
      · have hcard := Finset.card_lt_card hstrict
        have hbudget : n ≤ (phaseProgressSet (M : ℝ) v y).card + k := by omega
        have htail := ih y (walk_end_mem K v hwalk) hbudget
        have hcat := standardCircuitWalk_trans K v hwalk htail
        have hid : (4 * M ^ 2 + 1) + k * (4 * M ^ 2 + 1) =
            (k + 1) * (4 * M ^ 2 + 1) := by ring
        simpa only [hid] using hcat

/-- Matrix-free cubic routing from any feasible point to an extreme target.
No boundedness, basis-extension or source-theorem hypothesis is used. -/
theorem standardCircuitWalk_cubic_centered {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (v r : Fin n → ℝ)
    (hv : v ∈ Set.extremePoints ℝ (StandardSlice K v))
    (hr : r ∈ StandardSlice K v) :
    StandardCircuitWalk K v (17 * n ^ 3) r v := by
  by_cases hn0 : n = 0
  · subst n
    have hrv : r = v := by funext i; exact Fin.elim0 i
    subst r
    exact standardCircuitWalk_stationary K v v hv.1 _
  · have hn : 1 ≤ n := by omega
    let M : ℕ := max 2 n
    have hM : 2 ≤ M := le_max_left _ _
    have hnM : n ≤ M := le_max_right _ _
    have hMupper : M ≤ 2 * n := max_le (by omega) (by omega)
    have hwalk := standardCircuitWalk_phase_budget K M hM hnM v hv n r hr (by omega)
    exact standardCircuitWalk_mono K v hwalk (event_budget_le_cubic n M hn hMupper)

/-- Recenter at the target without changing the circuit directions or steps. -/
theorem standardCircuitWalk_cubic {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c r v : Fin n → ℝ)
    (hr : r ∈ StandardSlice K c)
    (hv : v ∈ Set.extremePoints ℝ (StandardSlice K c)) :
    StandardCircuitWalk K c (17 * n ^ 3) r v := by
  have hset := standardSlice_recenter K c v hv.1
  have hv' : v ∈ Set.extremePoints ℝ (StandardSlice K v) := by rwa [← hset]
  have hr' : r ∈ StandardSlice K v := by rwa [← hset]
  exact (standardCircuitWalk_recenter_iff K c v hv.1 (17 * n ^ 3) r v).mpr
    (standardCircuitWalk_cubic_centered K v r hv' hr')

/-- Discharge the formerly conditional source interface constructively. -/
theorem standard_cubic_circuit_bound : StandardCubicCircuitBound := by
  refine ⟨17, ?_⟩
  intro n K c u hu v hv
  exact standardCircuitWalk_cubic K c u v hu.1 hv

#print axioms norm_steps_or_phase_progress
#print axioms exists_bounded_progress_phase
#print axioms standardCircuitWalk_phase_budget
#print axioms standardCircuitWalk_cubic
#print axioms standard_cubic_circuit_bound
end HirschCircuit
