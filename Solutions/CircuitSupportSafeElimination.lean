import Solutions.CircuitWeightedNormStep
import Solutions.CircuitEliminationInvariant

set_option autoImplicit false
set_option maxHeartbeats 6000000
open scoped BigOperators

namespace HirschCircuit

/-! Candidate continuation; no Lean compilation was available in this session.
The reference is synchronized with the entire progress set, not just the
trapped target-positive coordinates. -/

/-- The relaxed coefficients satisfy every hypothesis of the checked scalar
elimination invariant. The bound is in ambient-coordinate M, not matrix rank. -/
theorem support_safe_parameters (M rho : ℝ)
    (hM : 2 ≤ M) (hrho : 0 ≤ rho) (hsmall : rho ≤ 1 / (2 * M ^ 2)) :
    let lam := 1 / (2 * M)
    let eta := (1 - lam) * rho / (1 - rho)
    rho < 1 ∧ 0 ≤ lam ∧ lam ≤ 1 ∧ 0 ≤ eta ∧
      M * lam ≤ 1 / 2 ∧ M * eta ≤ lam := by
  dsimp only
  have hMpos : 0 < M := by linarith
  have hMne : M ≠ 0 := ne_of_gt hMpos
  have hd1 : 0 < 2 * M := by positivity
  have hd2 : 0 < 2 * M ^ 2 := by positivity
  have htaulam : 1 / (2 * M ^ 2) ≤ 1 / (2 * M) := by
    apply (div_le_div_iff₀ hd2 hd1).2
    nlinarith
  have hlamhalf : 1 / (2 * M) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hd1).2
    linarith
  have hrholam := hsmall.trans htaulam
  have hrho1 : rho < 1 := by linarith
  have hlam1 : 1 / (2 * M) ≤ 1 := by linarith
  have heta := extrapolation_eta_bounds (1 / (2 * M)) rho
    hlam1 hrho hrholam hrho1
  have hlamM : M * (1 / (2 * M)) = (1 / 2 : ℝ) := by
    field_simp [hMne] <;> ring
  have hMtau : M * (1 / (2 * M ^ 2)) = 1 / (2 * M) := by
    field_simp [hMne] <;> ring
  refine ⟨hrho1, le_of_lt (one_div_pos.mpr hd1), hlam1, heta.1,
    le_of_eq hlamM, ?_⟩
  calc
    M * ((1 - 1 / (2 * M)) * rho / (1 - rho)) ≤ M * rho :=
      mul_le_mul_of_nonneg_left heta.2 (le_of_lt hMpos)
    _ ≤ M * (1 / (2 * M ^ 2)) :=
      mul_le_mul_of_nonneg_left hsmall (le_of_lt hMpos)
    _ = 1 / (2 * M) := hMtau

/-- Small total potential guarantees one positive maximal circuit step that
strictly grows the permanent progress set. This proves the actual event:
no event-existence assumption is imported or added to the theorem. -/
theorem exists_support_safe_elimination_step {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (M : ℕ) (v r x : Fin n → ℝ)
    (hM : 2 ≤ M) (hnM : n ≤ M)
    (hv : v ∈ Set.extremePoints ℝ (StandardSlice K v))
    (hr : r ∈ StandardSlice K v) (hx : x ∈ StandardSlice K v)
    (hphase : phaseProgressSet (M : ℝ) v r = phaseProgressSet (M : ℝ) v x)
    (hne : x ≠ v)
    (hsmall : referencePotential v r x ≤ 1 / (2 * (M : ℝ) ^ 2)) :
    ∃ y : Fin n → ℝ,
      StandardCircuitStep K v x y ∧
      phaseProgressSet (M : ℝ) v x ⊂ phaseProgressSet (M : ℝ) v y := by
  classical
  have hMnat : 0 < M := by omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMnat
  have hMreal : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) ≤ M := le_of_lt hMR
  let D : Finset (Fin n) := Finset.univ.filter fun i => v i = 0 ∧ 0 < x i
  have hD : D.Nonempty := by
    obtain ⟨i, hvi, hxi⟩ := exists_live_target_zero K v x hv hx hne
    exact ⟨i, by simp [D, hvi, hxi]⟩
  obtain ⟨q, hqD, hmaxratio⟩ := D.exists_max_image (fun i => x i / r i) hD
  have hq : v q = 0 ∧ 0 < x q := (Finset.mem_filter.mp hqD).2
  have hrq : 0 < r q := reference_positive_of_live (M : ℝ) v r x
    hr.2 hphase q hq.1 hq.2
  let rho : ℝ := x q / r q
  have hrho : 0 < rho := div_pos hq.2 hrq
  have hrhosmall : rho ≤ 1 / (2 * (M : ℝ) ^ 2) :=
    (referencePotential_ratio_le v r x hr.2 hx.2 q hq.1).trans hsmall
  let lam : ℝ := 1 / (2 * (M : ℝ))
  let eta : ℝ := (1 - lam) * rho / (1 - rho)
  obtain ⟨hrho1, hlam0, hlam1, heta0, hMlam, hMeta⟩ :=
    support_safe_parameters (M : ℝ) rho hMreal (le_of_lt hrho) hrhosmall
  have hden : 0 < 1 - rho := sub_pos.mpr hrho1
  have hdenne : 1 - rho ≠ 0 := ne_of_gt hden
  have hratio : ∀ i, v i = 0 → x i ≤ rho * r i := by
    intro i hvi
    by_cases hxi : x i = 0
    · rw [hxi]
      exact mul_nonneg (le_of_lt hrho) (hr.2 i)
    · have hxipos : 0 < x i := by
        rcases lt_or_eq_of_le (hx.2 i) with hp | he
        · exact hp
        · exact (hxi he.symm).elim
      have hiD : i ∈ D := by simp [D, hvi, hxipos]
      have hripos := reference_positive_of_live (M : ℝ) v r x
        hr.2 hphase i hvi hxipos
      exact (div_le_iff₀ hripos).mp (hmaxratio i hiD)
  have hqeq : x q = rho * r q := by
    dsimp [rho]
    exact (div_mul_cancel₀ (x q) (ne_of_gt hrq)).symm
  let delta : Fin n → ℝ := lam • (v - x) + eta • (x - r)
  have hdeltaK : delta ∈ K := by
    have hvx : v - x ∈ K := by
      simpa only [neg_sub] using K.neg_mem hx.1
    have hxr : x - r ∈ K := by
      have heq : x - r = (x - v) - (r - v) := by abel
      rw [heq]
      exact K.sub_mem hx.1 hr.1
    exact K.add_mem (K.smul_mem lam hvx) (K.smul_mem eta hxr)
  have hformula : ∀ i, v i = 0 →
      delta i = -x i + ((1 - lam) / (1 - rho)) * (x i - rho * r i) := by
    intro i hvi
    change lam * (v i - x i) + eta * (x i - r i) = _
    rw [hvi]
    dsimp [eta]
    field_simp [hdenne] <;> ring
  have hdeltaN : ∀ i, v i = 0 → delta i ≤ 0 := by
    intro i hvi
    rw [hformula i hvi]
    have hcoef : 0 ≤ (1 - lam) / (1 - rho) :=
      div_nonneg (sub_nonneg.mpr hlam1) (le_of_lt hden)
    have hprod := mul_nonpos_of_nonneg_of_nonpos hcoef
      (sub_nonpos.mpr (hratio i hvi))
    linarith [hx.2 i]
  have hdeltaq : delta q = -x q := by
    rw [hformula q hq.1]
    have hz : x q - rho * r q = 0 := sub_eq_zero.mpr hqeq
    rw [hz, mul_zero, add_zero]
  obtain ⟨gs, hlen, hall, hsumg⟩ :=
    exists_elementary_conformal_decomposition_le_n K delta hdeltaK
  have hsum : (gs.map (fun g => -g q)).sum = x q := by
    rw [circuit_list_sum_neg_coordinate, hsumg, hdeltaq, neg_neg]
  obtain ⟨g, hgmem, hscore⟩ := exists_mem_ge_average
    gs (fun g => -g q) M (x q) hMnat (hlen.trans hnM) hq.2 hsum
  obtain ⟨hgelem, hgconf⟩ := hall g hgmem
  have hS : 0 < -g q := (div_pos hq.2 hMR).trans_le hscore
  have hgq : g q < 0 := by linarith
  have hzero : ∀ i, x i = 0 → 0 ≤ g i := by
    apply elimination_direction_nonnegative_at_zero x r v g (M : ℝ) lam eta
      hv.1.2 heta0 (by simpa [lam, eta, mul_comm] using hMeta) hgconf
    intro i hxi
    exact same_phase_reference_trapped_of_current_zero (M : ℝ) v r x
      hphase hM0 hv.1.2 i hxi
  obtain ⟨alpha, ha, hfeas, hsat, hmax⟩ :=
    exists_positive_maximal_nonnegative_step x g hx.2 hzero ⟨q, hgq⟩
  have ha0 : 0 ≤ alpha := le_of_lt ha
  have hscoreM : x q ≤ (-g q) * (M : ℝ) := (div_le_iff₀ hMR).mp hscore
  have haM : alpha ≤ (M : ℝ) := by
    by_contra hn
    have hmul := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hS
    have hf := hfeas q
    nlinarith only [hscoreM, hmul, hf]
  let y : Fin n → ℝ := x + alpha • g
  have hstep : StandardCircuitStep K v x y :=
    standardCircuitStep_of_maximal_direction K v x g alpha
      hx hgelem ha hfeas hmax
  have htrapped : ∀ i, v i ≠ 0 → x i ≤ (M : ℝ) * v i →
      x i / 2 ≤ y i ∧ y i ≤ (M : ℝ) * v i := by
    intro i hvi hxi
    have hri := (same_phase_trapped_iff (M : ℝ) v r x hphase i hvi).2 hxi
    have hpiece := scalarConformalPiece_of_sign_abs (g i) (delta i)
      (hgconf i).1 (hgconf i).2
    change ScalarConformalPiece (g i)
      (lam * (v i - x i) + eta * (x i - r i)) at hpiece
    exact elimination_conformal_coordinate_bounds
      (M : ℝ) (v i) (x i) (r i) lam eta (g i) alpha hMreal
      (hv.1.2 i) (hx.2 i) (hr.2 i) hxi hri hlam0 heta0 hMlam hMeta
      hpiece ha0 haM
  have hnonbasic : ∀ i, v i = 0 → y i ≤ x i := by
    intro i hvi
    have hgi := conformalTo_coord_nonpos_of_right_nonpos hgconf (hdeltaN i hvi)
    change x i + alpha * g i ≤ x i
    have hprod := mul_nonpos_of_nonneg_of_nonpos ha0 hgi
    linarith
  have hmono : phaseProgressSet (M : ℝ) v x ⊆ phaseProgressSet (M : ℝ) v y := by
    apply phaseProgressSet_mono
    · intro i hvi hxi
      have hle := hnonbasic i hvi
      have hge : 0 ≤ y i := hfeas i
      rw [hxi] at hle
      exact le_antisymm hle hge
    · intro i hvi hxi
      exact (htrapped i hvi hxi).2
  obtain ⟨j, hgj, hblock⟩ := hsat
  have hyj : y j = 0 := hblock
  have hxj : 0 < x j := by
    rcases lt_or_eq_of_le (hx.2 j) with hp | he
    · exact hp
    · have hgj0 := hzero j he.symm
      linarith
  refine ⟨y, hstep, phaseProgressSet_ssubset_of_event (M : ℝ) v x y hmono ?_⟩
  by_cases hvj : v j = 0
  · exact ⟨j, Or.inl ⟨hvj, ne_of_gt hxj, hyj⟩⟩
  · have hnottrap : ¬ x j ≤ (M : ℝ) * v j := by
      intro htrap
      have hlo := (htrapped j hvj htrap).1
      rw [hyj] at hlo
      linarith
    have hytrap : y j ≤ (M : ℝ) * v j := by
      rw [hyj]
      exact mul_nonneg hM0 (hv.1.2 j)
    exact ⟨j, Or.inr ⟨hvj, hnottrap, hytrap⟩⟩

#print axioms support_safe_parameters
#print axioms exists_support_safe_elimination_step

end HirschCircuit
