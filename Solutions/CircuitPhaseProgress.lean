import Solutions.CircuitTargetSupport

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace HirschCircuit

/-- Coordinates that have made permanent phase progress toward a nonnegative
target: target-zero coordinates already at zero, and target-positive
coordinates already below the `M*v_i` trapped threshold. -/
noncomputable def phaseProgressSet {n : ℕ}
    (M : ℝ) (v x : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i =>
    if v i = 0 then x i = 0 else x i ≤ M * v i

@[simp] theorem mem_phaseProgressSet {n : ℕ}
    (M : ℝ) (v x : Fin n → ℝ) (i : Fin n) :
    i ∈ phaseProgressSet M v x ↔
      (if v i = 0 then x i = 0 else x i ≤ M * v i) := by
  simp [phaseProgressSet]

theorem phaseProgressSet_card_le {n : ℕ}
    (M : ℝ) (v x : Fin n → ℝ) :
    (phaseProgressSet M v x).card ≤ n := by
  have hsub : phaseProgressSet M v x ⊆ Finset.univ := Finset.subset_univ _
  have hcard := Finset.card_le_card hsub
  simpa using hcard

/-- Pointwise preservation of target-zero coordinates and trapped coordinates
makes the phase-progress set monotone. -/
theorem phaseProgressSet_mono {n : ℕ}
    (M : ℝ) (v x y : Fin n → ℝ)
    (hzero : ∀ i, v i = 0 → x i = 0 → y i = 0)
    (htrap : ∀ i, v i ≠ 0 → x i ≤ M * v i → y i ≤ M * v i) :
    phaseProgressSet M v x ⊆ phaseProgressSet M v y := by
  intro i hi
  simp only [mem_phaseProgressSet] at hi ⊢
  by_cases hv0 : v i = 0
  · simp only [hv0, if_pos]
    exact hzero i hv0 (by simpa [hv0] using hi)
  · simp only [hv0, if_neg]
    exact htrap i hv0 (by simpa [hv0] using hi)

/-- A newly zeroed target-zero coordinate or a newly trapped target-positive
coordinate strictly enlarges the finite progress set. -/
theorem phaseProgressSet_ssubset_of_event {n : ℕ}
    (M : ℝ) (v x y : Fin n → ℝ)
    (hmono : phaseProgressSet M v x ⊆ phaseProgressSet M v y)
    (hevent : ∃ i,
      (v i = 0 ∧ x i ≠ 0 ∧ y i = 0) ∨
      (v i ≠ 0 ∧ ¬ x i ≤ M * v i ∧ y i ≤ M * v i)) :
    phaseProgressSet M v x ⊂ phaseProgressSet M v y := by
  obtain ⟨i, hi⟩ := hevent
  refine ssubset_of_ne_of_subset ?_ hmono
  intro heq
  have hiff : i ∈ phaseProgressSet M v x ↔ i ∈ phaseProgressSet M v y := by
    rw [heq]
  rcases hi with ⟨hv0, hxi, hy0⟩ | ⟨hv0, hxi, hyi⟩
  · have hyMem : i ∈ phaseProgressSet M v y := by
      simp [mem_phaseProgressSet, hv0, hy0]
    have hxMem := hiff.mpr hyMem
    simp [mem_phaseProgressSet, hv0] at hxMem
    exact hxi hxMem
  · have hyMem : i ∈ phaseProgressSet M v y := by
      simp [mem_phaseProgressSet, hv0, hyi]
    have hxMem := hiff.mpr hyMem
    simp [mem_phaseProgressSet, hv0] at hxMem
    exact hxi hxMem

/-- Equal phase-progress sets synchronize the two invariants needed by the
support-safe reference rule. -/
theorem same_phase_zero_iff {n : ℕ}
    (M : ℝ) (v r x : Fin n → ℝ)
    (heq : phaseProgressSet M v r = phaseProgressSet M v x)
    (i : Fin n) (hv0 : v i = 0) :
    r i = 0 ↔ x i = 0 := by
  have hiff : i ∈ phaseProgressSet M v r ↔ i ∈ phaseProgressSet M v x := by
    rw [heq]
  simpa [mem_phaseProgressSet, hv0] using hiff

theorem same_phase_trapped_iff {n : ℕ}
    (M : ℝ) (v r x : Fin n → ℝ)
    (heq : phaseProgressSet M v r = phaseProgressSet M v x)
    (i : Fin n) (hv0 : v i ≠ 0) :
    r i ≤ M * v i ↔ x i ≤ M * v i := by
  have hiff : i ∈ phaseProgressSet M v r ↔ i ∈ phaseProgressSet M v x := by
    rw [heq]
  simpa [mem_phaseProgressSet, hv0] using hiff

/-- At a target-positive coordinate, a zero current value is necessarily
trapped, hence the phase reference was already trapped if no event occurred. -/
theorem same_phase_reference_trapped_of_current_zero {n : ℕ}
    (M : ℝ) (v r x : Fin n → ℝ)
    (heq : phaseProgressSet M v r = phaseProgressSet M v x)
    (hM : 0 ≤ M) (hv : ∀ i, 0 ≤ v i)
    (i : Fin n) (hxi : x i = 0) :
    r i ≤ M * v i := by
  by_cases hv0 : v i = 0
  · have hr0 := (same_phase_zero_iff M v r x heq i hv0).2 hxi
    rw [hr0, hv0]
    simp
  · apply (same_phase_trapped_iff M v r x heq i hv0).2
    rw [hxi]
    exact mul_nonneg hM (hv i)

/-- If every coordinate has entered the finite progress set, then all
coordinates outside the positive support of `v` are zero. Extremality then
forces the current point to be the target. -/
theorem eq_target_of_full_phase_progress {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ))
    (M : ℝ) (v x : Fin n → ℝ)
    (hvext : v ∈ Set.extremePoints ℝ (StandardSlice K v))
    (hx : x ∈ StandardSlice K v)
    (hfull : phaseProgressSet M v x = Finset.univ) :
    x = v := by
  apply eq_target_of_zero_off_support K v x hvext hx
  intro i hv0
  have hi : i ∈ phaseProgressSet M v x := by simp [hfull]
  simpa [mem_phaseProgressSet, hv0] using hi

/-- Strict progress can occur at most `n` times in any chain of phase-progress
sets. This cardinal form is the global phase counter used by the route proof. -/
theorem phase_progress_card_strict {n : ℕ}
    (M : ℝ) (v x y : Fin n → ℝ)
    (hstrict : phaseProgressSet M v x ⊂ phaseProgressSet M v y) :
    (phaseProgressSet M v x).card < (phaseProgressSet M v y).card :=
  Finset.card_lt_card hstrict

#print axioms phaseProgressSet_mono
#print axioms phaseProgressSet_ssubset_of_event
#print axioms same_phase_zero_iff
#print axioms same_phase_trapped_iff
#print axioms eq_target_of_full_phase_progress
#print axioms phase_progress_card_strict

end HirschCircuit
