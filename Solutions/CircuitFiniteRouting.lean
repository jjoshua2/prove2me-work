import Solutions.CircuitSupportSafeElimination
import Solutions.CircuitContractionBudget
import Solutions.CircuitStandardRecenter

set_option autoImplicit false
set_option maxHeartbeats 7000000

namespace HirschCircuit

/-! Candidate finite assembly of the support-safe route.
This file is uncompiled in the producing session. All geometric step
obligations are discharged through the two new constructive step proofs;
there is no assumed phase-existence or circuit-diameter theorem. -/

theorem standardCircuitWalk_const {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c x : Fin n → ℝ)
    (hx : x ∈ StandardSlice K c) (L : ℕ) :
    StandardCircuitWalk K c L x x := by
  exact ⟨fun _ => x, rfl, rfl, fun _ _ => hx, fun _ _ => Or.inl rfl⟩

theorem standardCircuitWalk_last_mem {n : ℕ}
    {K : Submodule ℝ (Fin n → ℝ)} {c u v : Fin n → ℝ} {L : ℕ}
    (h : StandardCircuitWalk K c L u v) : v ∈ StandardSlice K c := by
  obtain ⟨w, _, hwL, hmem, _⟩ := h
  simpa only [hwL] using hmem L (le_refl L)

theorem standardCircuitWalk_prepend {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c : Fin n → ℝ)
    {x y z : Fin n → ℝ} {L : ℕ}
    (hx : x ∈ StandardSlice K c)
    (hxy : x = y ∨ StandardCircuitStep K c x y)
    (h : StandardCircuitWalk K c L y z) :
    StandardCircuitWalk K c (L + 1) x z := by
  obtain ⟨w, hw0, hwL, hmem, hsteps⟩ := h
  refine ⟨(fun j => match j with | 0 => x | k + 1 => w k), rfl, ?_, ?_, ?_⟩
  · exact hwL
  · intro j hj
    cases j with
    | zero => exact hx
    | succ j => exact hmem j (by omega)
  · intro j hj
    cases j with
    | zero =>
        change x = w 0 ∨ StandardCircuitStep K c x (w 0)
        simpa only [hw0] using hxy
    | succ j => exact hsteps j (by omega)

theorem standardCircuitWalk_one {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c : Fin n → ℝ)
    {x y : Fin n → ℝ} (h : StandardCircuitStep K c x y) :
    StandardCircuitWalk K c 1 x y := by
  exact standardCircuitWalk_prepend K c h.1 (Or.inr h)
    (standardCircuitWalk_const K c y h.2.1 0)

theorem standardCircuitWalk_append {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c : Fin n → ℝ)
    {u v w : Fin n → ℝ} {L Q : ℕ}
    (h1 : StandardCircuitWalk K c L u v)
    (h2 : StandardCircuitWalk K c Q v w) :
    StandardCircuitWalk K c (L + Q) u w := by
  induction L generalizing u with
  | zero =>
      obtain ⟨f, hf0, hfL, _, _⟩ := h1
      have huv : u = v := hf0.symm.trans hfL
      simpa only [Nat.zero_add, huv] using h2
  | succ L ih =>
      obtain ⟨f, hf0, hfL, hmem, hsteps⟩ := h1
      have htail : StandardCircuitWalk K c L (f 1) v := by
        refine ⟨fun j => f (j + 1), rfl, hfL, ?_, ?_⟩
        · intro j hj
          exact hmem (j + 1) (by omega)
        · intro j hj
          exact hsteps (j + 1) (by omega)
      have hu : u ∈ StandardSlice K c := by
        simpa only [hf0] using hmem 0 (Nat.zero_le _)
      have hfirst : u = f 1 ∨ StandardCircuitStep K c u (f 1) := by
        simpa only [hf0, Nat.zero_add] using hsteps 0 (Nat.succ_pos L)
      have hjoined := standardCircuitWalk_prepend K c hu hfirst (ih (u := f 1) htail)
      simpa only [Nat.succ_add, Nat.succ_eq_add_one] using hjoined

theorem standardCircuitWalk_mono {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c : Fin n → ℝ)
    {L Q : ℕ} {u v : Fin n → ℝ}
    (h : StandardCircuitWalk K c L u v) (hLQ : L ≤ Q) :
    StandardCircuitWalk K c Q u v := by
  obtain ⟨w, hw0, hwL, hmem, hsteps⟩ := h
  refine ⟨fun j => w (min j L), ?_, ?_, ?_, ?_⟩
  · simpa using hw0
  · simpa only [Nat.min_eq_right hLQ] using hwL
  · intro j _
    exact hmem _ (Nat.min_le_right _ _)
  · intro j _
    by_cases hj : j < L
    · simpa only [Nat.min_eq_left (Nat.le_of_lt hj),
        Nat.min_eq_left (Nat.succ_le_iff.mpr hj)] using hsteps j hj
    · left
      change w (min j L) = w (min (j + 1) L)
      rw [Nat.min_eq_right (Nat.le_of_not_gt hj),
        Nat.min_eq_right (by omega : L ≤ j + 1)]

/-- A fixed block of norm steps either reaches the target, produces a permanent
progress event, or contracts below the elimination threshold. Once an event
occurs, the rest of this *proof witness* is stationary padding: it is not a
zero-length augmentation along an outward circuit direction. -/
theorem exists_phase_progress_walk {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (M : ℕ) (v r : Fin n → ℝ)
    (hM : 2 ≤ M) (hnM : n ≤ M)
    (hv : v ∈ Set.extremePoints ℝ (StandardSlice K v))
    (hr : r ∈ StandardSlice K v) :
    ∃ y : Fin n → ℝ,
      StandardCircuitWalk K v (4 * M ^ 2 + 1) r y ∧
      (y = v ∨ phaseProgressSet (M : ℝ) v r ⊂ phaseProgressSet (M : ℝ) v y) := by
  classical
  let q : ℝ := 1 - 1 / (M : ℝ)
  have hMnat : 0 < M := by omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMnat
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hq0 : 0 ≤ q := by
    have hdiv : 1 / (M : ℝ) ≤ 1 := (div_le_one hMR).2 hMone
    dsimp [q]
    linarith
  have hblocks : ∀ k : ℕ, ∃ x : Fin n → ℝ,
      StandardCircuitWalk K v k r x ∧
      (x = v ∨ phaseProgressSet (M : ℝ) v r ⊂ phaseProgressSet (M : ℝ) v x ∨
        (phaseProgressSet (M : ℝ) v r = phaseProgressSet (M : ℝ) v x ∧
          referencePotential v r x ≤ (M : ℝ) * q ^ k)) := by
    intro k
    induction k with
    | zero =>
        refine ⟨r, standardCircuitWalk_const K v r hr 0, Or.inr (Or.inr ⟨rfl, ?_⟩)⟩
        have hnMr : (n : ℝ) ≤ M := by exact_mod_cast hnM
        simpa only [pow_zero, mul_one] using (referencePotential_self_le_n v r).trans hnMr
    | succ k ih =>
        obtain ⟨x, hwalk, hcase⟩ := ih
        rcases hcase with hxv | hstrict | ⟨hphase, hpot⟩
        · exact ⟨x, standardCircuitWalk_mono K v hwalk (by omega), Or.inl hxv⟩
        · exact ⟨x, standardCircuitWalk_mono K v hwalk (by omega), Or.inr (Or.inl hstrict)⟩
        · by_cases hxv : x = v
          · exact ⟨x, standardCircuitWalk_mono K v hwalk (by omega), Or.inl hxv⟩
          · have hx := standardCircuitWalk_last_mem hwalk
            obtain ⟨y, hstep, hmono, _hN, hcontract⟩ :=
              exists_weighted_norm_step K M v r x hM hnM hv hr.2 hx hphase hxv
            have hjoined : StandardCircuitWalk K v (k + 1) r y :=
              standardCircuitWalk_append K v hwalk (standardCircuitWalk_one K v hstep)
            have hmonor : phaseProgressSet (M : ℝ) v r ⊆ phaseProgressSet (M : ℝ) v y := by
              rw [hphase]
              exact hmono
            refine ⟨y, hjoined, ?_⟩
            by_cases heq : phaseProgressSet (M : ℝ) v r = phaseProgressSet (M : ℝ) v y
            · refine Or.inr (Or.inr ⟨heq, ?_⟩)
              change referencePotential v r y ≤ (M : ℝ) * q ^ (k + 1)
              change referencePotential v r y ≤ q * referencePotential v r x at hcontract
              calc
                referencePotential v r y ≤ q * referencePotential v r x := hcontract
                _ ≤ q * ((M : ℝ) * q ^ k) := mul_le_mul_of_nonneg_left hpot hq0
                _ = (M : ℝ) * q ^ (k + 1) := by rw [pow_succ]; ring
            · exact Or.inr (Or.inl (ssubset_of_ne_of_subset heq hmonor))
  obtain ⟨x, hwalk, hcase⟩ := hblocks (4 * M ^ 2)
  rcases hcase with hxv | hstrict | ⟨hphase, hpot⟩
  · exact ⟨x, standardCircuitWalk_mono K v hwalk (by omega), Or.inl hxv⟩
  · exact ⟨x, standardCircuitWalk_mono K v hwalk (by omega), Or.inr hstrict⟩
  · by_cases hxv : x = v
    · exact ⟨x, standardCircuitWalk_mono K v hwalk (by omega), Or.inl hxv⟩
    · have hsmall : referencePotential v r x ≤ 1 / (2 * (M : ℝ) ^ 2) := by
        exact hpot.trans (by simpa only [q] using contraction_to_elimination_threshold M hM)
      obtain ⟨y, hstep, hstrict⟩ := exists_support_safe_elimination_step K M v r x
        hM hnM hv hr (standardCircuitWalk_last_mem hwalk) hphase hxv hsmall
      refine ⟨y, standardCircuitWalk_append K v hwalk (standardCircuitWalk_one K v hstep),
        Or.inr ?_⟩
      rw [hphase]
      exact hstrict

/-- Induction on the remaining number of permanent progress coordinates.
Each invocation starts a fresh phase at the current point; no stale reference
is carried across a strict event. -/
theorem standardCircuitWalk_phase_budget {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (M : ℕ) (v x : Fin n → ℝ)
    (hM : 2 ≤ M) (hnM : n ≤ M)
    (hv : v ∈ Set.extremePoints ℝ (StandardSlice K v))
    (hx : x ∈ StandardSlice K v) :
    StandardCircuitWalk K v (n * (4 * M ^ 2 + 1)) x v := by
  classical
  let B : ℕ := 4 * M ^ 2 + 1
  have aux : ∀ k : ℕ, ∀ x : Fin n → ℝ,
      x ∈ StandardSlice K v →
      n ≤ (phaseProgressSet (M : ℝ) v x).card + k →
      StandardCircuitWalk K v (k * B) x v := by
    intro k
    induction k with
    | zero =>
        intro x hx hk
        have hcard : n ≤ (phaseProgressSet (M : ℝ) v x).card := by simpa using hk
        have hfull : phaseProgressSet (M : ℝ) v x = Finset.univ := by
          apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
          simpa using hcard
        have hxv := eq_target_of_full_phase_progress K (M : ℝ) v x hv hx hfull
        subst x
        simpa only [Nat.zero_mul] using standardCircuitWalk_const K v v hv.1 0
    | succ k ih =>
        intro x hx hk
        obtain ⟨y, hphasewalk, hcase⟩ := exists_phase_progress_walk K M v x hM hnM hv hx
        have hy := standardCircuitWalk_last_mem hphasewalk
        have htail : StandardCircuitWalk K v (k * B) y v := by
          rcases hcase with hyv | hstrict
          · subst y
            exact standardCircuitWalk_const K v v hv.1 (k * B)
          · apply ih y hy
            have hlt := Finset.card_lt_card hstrict
            omega
        have hjoined := standardCircuitWalk_append K v hphasewalk htail
        change StandardCircuitWalk K v (B + k * B) x v at hjoined
        simpa only [Nat.succ_mul, Nat.add_comm] using hjoined
  exact aux n x hx (by omega)

/-- An explicit ambient-coordinate cubic envelope. All circuit directions
remain elementary in the original fixed K, and all nonstationary steps are
positive maximal augmentations. -/
theorem standardCircuitWalk_explicit_cubic {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (v x : Fin n → ℝ)
    (hv : v ∈ Set.extremePoints ℝ (StandardSlice K v))
    (hx : x ∈ StandardSlice K v) :
    StandardCircuitWalk K v (17 * n ^ 3) x v := by
  by_cases hn : n = 0
  · subst n
    have hxv : x = v := by
      funext i
      exact Fin.elim0 i
    subst x
    simpa using standardCircuitWalk_const K v v hv.1 0
  · have hn1 : 1 ≤ n := by omega
    let M : ℕ := max 2 n
    have hM : 2 ≤ M := le_max_left _ _
    have hnM : n ≤ M := le_max_right _ _
    have hMupper : M ≤ 2 * n := by
      dsimp [M]
      apply max_le <;> omega
    have hwalk := standardCircuitWalk_phase_budget K M v x hM hnM hv hx
    exact standardCircuitWalk_mono K v hwalk (event_budget_le_cubic n M hn1 hMupper)

/-- Discharge the former source hypothesis with an explicit constructive
candidate, rather than assuming the cubic bound or importing the target. -/
theorem standardCubicCircuitBound_explicit : StandardCubicCircuitBound := by
  refine ⟨17, ?_⟩
  intro n K c u hu v hv
  have hset := standardSlice_recenter K c v hv.1
  have hv' : v ∈ Set.extremePoints ℝ (StandardSlice K v) := by
    rwa [← hset]
  have hu' : u ∈ StandardSlice K v := by
    rw [← hset]
    exact hu.1
  exact (standardCircuitWalk_recenter_iff K c v hv.1 (17 * n ^ 3) u v).mpr
    (standardCircuitWalk_explicit_cubic K v u hv' hu')

#print axioms exists_phase_progress_walk
#print axioms standardCircuitWalk_phase_budget
#print axioms standardCircuitWalk_explicit_cubic
#print axioms standardCubicCircuitBound_explicit

end HirschCircuit
