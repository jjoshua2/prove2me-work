import Solutions.CircuitConformalDecomposition
import Solutions.CircuitStandardMaximalStep
import Solutions.CircuitPhaseProgress
import Solutions.CircuitAveraging
import Solutions.CircuitEliminationInvariant

set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped BigOperators

namespace HirschCircuit

private theorem list_neg_eval_sum {n : ℕ}
    (gs : List (Fin n → ℝ)) (q : Fin n) :
    (gs.map fun g => -g q).sum = -(gs.sum q) := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
      simp only [List.map_cons, List.sum_cons, Pi.add_apply]
      rw [ih]
      ring

/-- The support-safe elimination step. The hypotheses describe its scalar
parameters and displacement, not an assumed step or progress conclusion.
A conformal elementary piece is selected by averaging, augmented maximally,
and proved to create a new target-zero or trapped coordinate. -/
theorem exists_support_safe_elimination_step {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (M : ℕ)
    (hM : 2 ≤ M) (hnM : n ≤ M)
    (v r x : Fin n → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (hr : r ∈ StandardSlice K v) (hx : x ∈ StandardSlice K v)
    (heq : phaseProgressSet (M : ℝ) v r = phaseProgressSet (M : ℝ) v x)
    (lam eta : ℝ) (hlam : 0 ≤ lam) (heta : 0 ≤ eta)
    (hlamM : (M : ℝ) * lam ≤ 1 / 2) (hetaM : (M : ℝ) * eta ≤ lam)
    (hN : ∀ i, v i = 0 → lam * (v i - x i) + eta * (x i - r i) ≤ 0)
    (q : Fin n) (hxq : 0 < x q)
    (hq : lam * (v q - x q) + eta * (x q - r q) = -x q) :
    ∃ y : Fin n → ℝ,
      StandardCircuitStep K v x y ∧
      phaseProgressSet (M : ℝ) v x ⊂ phaseProgressSet (M : ℝ) v y ∧
      (∀ i, v i = 0 → y i ≤ x i) ∧
      ∀ i, v i ≠ 0 → x i ≤ (M : ℝ) * v i → x i / 2 ≤ y i := by
  classical
  have hMpos : 0 < M := by omega
  have hMr : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMrpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hMr0 : (0 : ℝ) ≤ (M : ℝ) := le_of_lt hMrpos
  let delta : Fin n → ℝ := lam • (v - x) + eta • (x - r)
  have hxr : x - r ∈ K := by
    have hid : x - r = (x - v) - (r - v) := by abel
    rw [hid]
    exact K.sub_mem hx.1 hr.1
  have hvx : v - x ∈ K := by simpa only [neg_sub] using K.neg_mem hx.1
  have hdelta : delta ∈ K := K.add_mem (K.smul_mem lam hvx) (K.smul_mem eta hxr)
  have hdeltaq : delta q = -x q := hq
  obtain ⟨gs, hlen, hall, hsum⟩ :=
    exists_elementary_conformal_decomposition_le_n K delta hdelta
  have hsumq : (gs.map fun g => -g q).sum = x q := by
    rw [list_neg_eval_sum, hsum, hdeltaq, neg_neg]
  obtain ⟨g, hgmem, hscore⟩ :=
    exists_mem_ge_average gs (fun g => -g q) M (x q) hMpos (hlen.trans hnM) hxq hsumq
  obtain ⟨hgelem, hgconf⟩ := hall g hgmem
  have havg : 0 < x q / (M : ℝ) := div_pos hxq hMrpos
  have hgq : g q < 0 := by linarith
  have hzero : ∀ i, x i = 0 → 0 ≤ g i := by
    intro i hxi
    apply conformalTo_coord_nonneg_of_right_nonneg hgconf
    have href := same_phase_reference_trapped_of_current_zero
      (M : ℝ) v r x heq hMr0 hv i hxi
    have h1 := mul_le_mul_of_nonneg_left href heta
    have h2 := mul_le_mul_of_nonneg_right hetaM (hv i)
    change 0 ≤ lam * (v i - x i) + eta * (x i - r i)
    rw [hxi]
    nlinarith only [h1, h2]
  obtain ⟨alpha, ha, hfeas, hsat, hmax⟩ :=
    exists_positive_maximal_nonnegative_step x g hx.2 hzero ⟨q, hgq⟩
  let y : Fin n → ℝ := x + alpha • g
  have hstep : StandardCircuitStep K v x y :=
    standardCircuitStep_of_maximal_direction K v x g alpha hx hgelem ha hfeas hmax
  have haM : alpha ≤ (M : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hscore (le_of_lt ha)
    have hqfeas := hfeas q
    have hcancel : (x q / (M : ℝ)) * (M : ℝ) = x q :=
      div_mul_cancel₀ _ (ne_of_gt hMrpos)
    nlinarith only [hmul, hqfeas, hcancel, havg]
  have htrap : ∀ i, v i ≠ 0 → x i ≤ (M : ℝ) * v i →
      x i / 2 ≤ y i ∧ y i ≤ (M : ℝ) * v i := by
    intro i hvi hxi
    have href := (same_phase_trapped_iff (M : ℝ) v r x heq i hvi).mpr hxi
    have hpiece := scalarConformalPiece_of_sign_abs (g i) (delta i)
      (hgconf i).1 (hgconf i).2
    exact elimination_conformal_coordinate_bounds (M : ℝ) (v i) (x i) (r i)
      lam eta (g i) alpha hMr (hv i) (hx.2 i) (hr.2 i) hxi href
      hlam heta hlamM hetaM hpiece (le_of_lt ha) haM
  have hNmono : ∀ i, v i = 0 → y i ≤ x i := by
    intro i hvi
    have hgi : g i ≤ 0 := conformalTo_coord_nonpos_of_right_nonpos hgconf (hN i hvi)
    change x i + alpha * g i ≤ x i
    have hmul := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha) hgi
    linarith
  have hprogress : phaseProgressSet (M : ℝ) v x ⊆ phaseProgressSet (M : ℝ) v y := by
    apply phaseProgressSet_mono
    · intro i hvi hxi
      have hm := hNmono i hvi
      have hy0 := hstep.2.1.2 i
      linarith
    · intro i hvi hxi
      exact (htrap i hvi hxi).2
  obtain ⟨i, hgi, hblocked⟩ := hsat
  have hxi : 0 < x i := by
    by_contra hn
    have hxi0 : x i = 0 := le_antisymm (le_of_not_gt hn) (hx.2 i)
    have hz := hzero i hxi0
    linarith
  have hyi : y i = 0 := hblocked
  have hevent : ∃ i,
      (v i = 0 ∧ x i ≠ 0 ∧ y i = 0) ∨
      (v i ≠ 0 ∧ ¬ x i ≤ (M : ℝ) * v i ∧ y i ≤ (M : ℝ) * v i) := by
    refine ⟨i, ?_⟩
    by_cases hvi : v i = 0
    · exact Or.inl ⟨hvi, ne_of_gt hxi, hyi⟩
    · right
      refine ⟨hvi, ?_, ?_⟩
      · intro htrapped
        have hb := (htrap i hvi htrapped).1
        rw [hyi] at hb
        linarith
      · rw [hyi]
        exact mul_nonneg hMr0 (hv i)
  refine ⟨y, hstep, phaseProgressSet_ssubset_of_event (M : ℝ) v x y hprogress hevent,
    hNmono, ?_⟩
  intro j hj htrapj
  exact (htrap j hj htrapj).1

#print axioms exists_support_safe_elimination_step
end HirschCircuit
