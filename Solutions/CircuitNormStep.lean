import Solutions.CircuitConformalDecomposition
import Solutions.CircuitStandardMaximalStep
import Solutions.CircuitPhaseProgress
import Solutions.CircuitAveraging

set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped BigOperators

namespace HirschCircuit

/-- Target-zero coordinates that are still live relative to the fixed phase
reference `r`. -/
noncomputable def liveZeroSet {n : ℕ} (v r : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => v i = 0 ∧ r i ≠ 0

@[simp] theorem mem_liveZeroSet {n : ℕ}
    (v r : Fin n → ℝ) (i : Fin n) :
    i ∈ liveZeroSet v r ↔ v i = 0 ∧ r i ≠ 0 := by
  simp [liveZeroSet]

/-- Fixed-reference phase potential on the still-live target-zero coordinates. -/
noncomputable def phasePotential {n : ℕ}
    (v r x : Fin n → ℝ) : ℝ :=
  ∑ i ∈ liveZeroSet v r, x i / r i

/-- Score of a circuit piece for decreasing the fixed-reference phase
potential. -/
noncomputable def normScore {n : ℕ}
    (v r g : Fin n → ℝ) : ℝ :=
  ∑ i ∈ liveZeroSet v r, (-g i) / r i

theorem liveZero_ref_pos {n : ℕ}
    {v r : Fin n → ℝ} (hr : ∀ i, 0 ≤ r i)
    {i : Fin n} (hi : i ∈ liveZeroSet v r) : 0 < r i := by
  have hne := (mem_liveZeroSet v r i).mp hi |>.2
  exact lt_of_le_of_ne (hr i) (Ne.symm hne)

theorem phasePotential_nonneg {n : ℕ}
    (v r x : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hx : ∀ i, 0 ≤ x i) : 0 ≤ phasePotential v r x := by
  unfold phasePotential
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro _ _
  exact div_nonneg (hx i) (hr i)

theorem normScore_add {n : ℕ}
    (v r g h : Fin n → ℝ) :
    normScore v r (g + h) = normScore v r g + normScore v r h := by
  unfold normScore
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro _ _
  simp only [Pi.add_apply]
  ring

theorem normScore_zero {n : ℕ} (v r : Fin n → ℝ) :
    normScore v r 0 = 0 := by
  simp [normScore]

theorem normScore_list_sum {n : ℕ}
    (v r : Fin n → ℝ) (gs : List (Fin n → ℝ)) :
    normScore v r gs.sum = (gs.map (normScore v r)).sum := by
  induction gs with
  | nil => simp [normScore_zero]
  | cons g gs ih =>
      simp only [List.sum_cons, List.map_cons, List.sum_cons]
      rw [normScore_add, ih]

theorem normScore_target_sub_eq_potential {n : ℕ}
    (v r x : Fin n → ℝ) :
    normScore v r (v - x) = phasePotential v r x := by
  unfold normScore phasePotential
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro _ _
  have hv0 := (mem_liveZeroSet v r i).mp hi |>.1
  rw [hv0]
  simp only [Pi.sub_apply]
  ring

theorem normScore_nonneg_of_conformal {n : ℕ}
    (v r x g : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hx : ∀ i, 0 ≤ x i)
    (hg : ConformalTo g (v - x)) :
    0 ≤ normScore v r g := by
  unfold normScore
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro _ _
  have himem := (mem_liveZeroSet v r i).mp hi
  have hrp := liveZero_ref_pos hr hi
  have hgi : g i ≤ 0 := by
    apply conformalTo_coord_nonpos_of_right_nonpos hg
    change v i - x i ≤ 0
    rw [himem.1]
    linarith [hx i]
  exact div_nonneg (neg_nonneg.mpr hgi) (le_of_lt hrp)

theorem phasePotential_step {n : ℕ}
    (v r x g : Fin n → ℝ) (α : ℝ) :
    phasePotential v r (x + α • g) =
      phasePotential v r x - α * normScore v r g := by
  unfold phasePotential normScore
  rw [Finset.mul_sum]
  rw [Finset.sum_sub_distrib]
  apply congrArg₂ (· - ·) rfl
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro _ _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- One maximal norm-reduction circuit step. A high-scoring elementary piece
of `v-x` exists by the finite conformal decomposition and averaging lemma. Its
true maximal augmentation has `1 ≤ α ≤ M`, contracts the fixed-reference
phase potential by at least the factor `1-1/M`, preserves all existing phase
progress, and never increases a target-zero coordinate. -/
theorem exists_norm_reduction_step {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ))
    (M : ℕ) (hM : 0 < M) (hnM : n ≤ M)
    (v r x : Fin n → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hr : ∀ i, 0 ≤ r i)
    (hx : x ∈ StandardSlice K v)
    (hW : 0 < phasePotential v r x) :
    ∃ y g : Fin n → ℝ, ∃ α : ℝ,
      0 < α ∧ 1 ≤ α ∧ α ≤ (M : ℝ) ∧
      StandardCircuitStep K v x y ∧
      y = x + α • g ∧
      0 ≤ phasePotential v r y ∧
      phasePotential v r y ≤
        (1 - 1 / (M : ℝ)) * phasePotential v r x ∧
      phaseProgressSet (M : ℝ) v x ⊆ phaseProgressSet (M : ℝ) v y ∧
      ∀ i, v i = 0 → y i ≤ x i := by
  classical
  have hzK : v - x ∈ K := by
    have hneg := K.neg_mem hx.1
    simpa [neg_sub] using hneg
  obtain ⟨gs, hlenN, hall, hsum⟩ :=
    exists_elementary_conformal_decomposition_le_n K (v - x) hzK
  have hlenM : gs.length ≤ M := hlenN.trans hnM
  let W : ℝ := phasePotential v r x
  have hscoreSum : (gs.map (normScore v r)).sum = W := by
    rw [← normScore_list_sum, hsum, normScore_target_sub_eq_potential]
    rfl
  obtain ⟨g, hgmem, hscore⟩ :=
    exists_mem_ge_average gs (normScore v r) M W hM hlenM (by simpa [W] using hW) hscoreSum
  obtain ⟨hgelem, hgconf⟩ := hall g hgmem
  have hMr : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have havgpos : 0 < W / (M : ℝ) := div_pos (by simpa [W] using hW) hMr
  have hSpos : 0 < normScore v r g := lt_of_lt_of_le havgpos hscore
  have hneg : ∃ i, g i < 0 := by
    by_contra hn
    push_neg at hn
    have hnonpos : normScore v r g ≤ 0 := by
      unfold normScore
      apply Finset.sum_nonpos
      intro i hi
      apply Finset.sum_nonpos
      intro _ _
      have hrp := liveZero_ref_pos hr hi
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hn i)) (le_of_lt hrp)
    linarith
  have hzero : ∀ i, x i = 0 → 0 ≤ g i := by
    intro i hxi
    apply conformalTo_coord_nonneg_of_right_nonneg hgconf
    change 0 ≤ v i - x i
    rw [hxi]
    simpa using hv i
  obtain ⟨α, hα, hfeas, _hsat, hmax⟩ :=
    exists_positive_maximal_nonnegative_step x g hx.2 hzero hneg
  let y : Fin n → ℝ := x + α • g
  have hstep : StandardCircuitStep K v x y := by
    dsimp [y]
    exact standardCircuitStep_of_maximal_direction K v x g α hx hgelem hα hfeas hmax
  have honeFeas := conformal_piece_feasible_at_one x v g hx.2 hv hgconf
  have hα1 : 1 ≤ α := by
    by_contra hn
    have hlt : α < 1 := lt_of_not_ge hn
    obtain ⟨i, hi⟩ := hmax 1 hlt
    have hfi := honeFeas i
    linarith
  have hWnew : 0 ≤ phasePotential v r y := by
    apply phasePotential_nonneg v r y hr
    intro i
    dsimp [y]
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hfeas i
  have hupdate : phasePotential v r y = W - α * normScore v r g := by
    dsimp [y]
    rw [phasePotential_step]
    rfl
  have hαSle : α * normScore v r g ≤ W := by
    rw [hupdate] at hWnew
    linarith
  have hαavg : α * (W / (M : ℝ)) ≤ W := by
    exact (mul_le_mul_of_nonneg_left hscore (le_of_lt hα)).trans hαSle
  have hcancel : (W / (M : ℝ)) * (M : ℝ) = W := by
    exact div_mul_cancel₀ W (ne_of_gt hMr)
  have hαM : α ≤ (M : ℝ) := by
    nlinarith only [hαavg, hcancel, havgpos]
  have hSleαS : normScore v r g ≤ α * normScore v r g := by
    nlinarith only [hα1, hSpos]
  have havgleαS : W / (M : ℝ) ≤ α * normScore v r g := hscore.trans hSleαS
  have hcontract : phasePotential v r y ≤
      (1 - 1 / (M : ℝ)) * phasePotential v r x := by
    rw [hupdate]
    change W - α * normScore v r g ≤ (1 - 1 / (M : ℝ)) * W
    nlinarith only [havgleαS]
  have hM1nat : 1 ≤ M := hM
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1nat
  have hprogress : phaseProgressSet (M : ℝ) v x ⊆ phaseProgressSet (M : ℝ) v y := by
    apply phaseProgressSet_mono
    · intro i hvi hxi
      have hz0 : (v - x) i = 0 := by
        simp [Pi.sub_apply, hvi, hxi]
      have hgi0 := conformalTo_eq_zero_of_right_eq_zero hgconf hz0
      dsimp [y]
      simp [hxi, hgi0]
    · intro i _ htrap
      dsimp [y]
      exact norm_step_preserves_trapped x v g hgconf (M : ℝ) α hM1
        (le_of_lt hα) hαM i (hx.2 i) htrap
  have hzeroMono : ∀ i, v i = 0 → y i ≤ x i := by
    intro i hvi
    have hgi : g i ≤ 0 := by
      apply conformalTo_coord_nonpos_of_right_nonpos hgconf
      change v i - x i ≤ 0
      rw [hvi]
      linarith [hx.2 i]
    dsimp [y]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hα) hgi
    linarith
  exact ⟨y, g, α, hα, hα1, hαM, hstep, rfl, hWnew, hcontract, hprogress, hzeroMono⟩

#print axioms phasePotential_step
#print axioms exists_norm_reduction_step

end HirschCircuit
