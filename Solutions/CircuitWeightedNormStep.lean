import Solutions.CircuitConformalDecomposition
import Solutions.CircuitAveraging
import Solutions.CircuitStandardMaximalStep
import Solutions.CircuitPhaseProgress

set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped BigOperators

namespace HirschCircuit

/-! Candidate continuation against a24d31a77362801e9f6f9ff3530d0ba97c803e7a.
This file has not been checked by Lean in the producing session. -/

/-- Reference weights only on coordinates where the target is zero.
At a zero reference coordinate the reciprocal is zero; phase equality will
ensure that the current coordinate is also zero. -/
noncomputable def targetZeroWeight {n : ℕ}
    (v r : Fin n → ℝ) (i : Fin n) : ℝ :=
  if v i = 0 then (r i)⁻¹ else 0

/-- The phase potential as a linear functional. Using linearity avoids
repeated exchanges of finite coordinate sums and lists of circuit pieces. -/
noncomputable def referencePotential {n : ℕ}
    (v r : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, targetZeroWeight v r i * x i
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    change (∑ i, targetZeroWeight v r i * (a * x i)) =
      a * ∑ i, targetZeroWeight v r i * x i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

@[simp] theorem referencePotential_apply {n : ℕ}
    (v r x : Fin n → ℝ) :
    referencePotential v r x = ∑ i, targetZeroWeight v r i * x i := rfl

theorem targetZeroWeight_nonneg {n : ℕ}
    (v r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (i : Fin n) :
    0 ≤ targetZeroWeight v r i := by
  by_cases hi : v i = 0
  · simp only [targetZeroWeight, if_pos hi]
    exact inv_nonneg.mpr (hr i)
  · simp [targetZeroWeight, hi]

theorem referencePotential_nonneg {n : ℕ}
    (v r x : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ referencePotential v r x := by
  change 0 ≤ ∑ i, targetZeroWeight v r i * x i
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (targetZeroWeight_nonneg v r hr i) (hx i)

@[simp] theorem referencePotential_target {n : ℕ}
    (v r : Fin n → ℝ) : referencePotential v r v = 0 := by
  change (∑ i, targetZeroWeight v r i * v i) = 0
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : v i = 0 <;> simp [targetZeroWeight, hi]

theorem referencePotential_self_le_n {n : ℕ} (v r : Fin n → ℝ) :
    referencePotential v r r ≤ (n : ℝ) := by
  calc
    referencePotential v r r ≤ ∑ _i : Fin n, (1 : ℝ) := by
      change (∑ i, targetZeroWeight v r i * r i) ≤ ∑ _i : Fin n, (1 : ℝ)
      apply Finset.sum_le_sum
      intro i _
      by_cases hv : v i = 0 <;> by_cases hr : r i = 0 <;>
        simp [targetZeroWeight, hv, hr]
    _ = (n : ℝ) := by simp

/-- Each nonnegative coordinate ratio is bounded by the whole potential. -/
theorem referencePotential_ratio_le {n : ℕ}
    (v r x : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (hx : ∀ i, 0 ≤ x i)
    (i : Fin n) (hvi : v i = 0) :
    x i / r i ≤ referencePotential v r x := by
  change x i / r i ≤ ∑ j, targetZeroWeight v r j * x j
  calc
    x i / r i = targetZeroWeight v r i * x i := by
      simp only [targetZeroWeight, if_pos hvi, div_eq_mul_inv, mul_comm]
    _ ≤ ∑ j, targetZeroWeight v r j * x j :=
      Finset.single_le_sum
        (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
          mul_nonneg (targetZeroWeight_nonneg v r hr j) (hx j))
        (Finset.mem_univ i)

/-- Nontermination supplies a live target-zero coordinate. -/
theorem exists_live_target_zero {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (v x : Fin n → ℝ)
    (hv : v ∈ Set.extremePoints ℝ (StandardSlice K v))
    (hx : x ∈ StandardSlice K v) (hne : x ≠ v) :
    ∃ i, v i = 0 ∧ 0 < x i := by
  by_contra hnone
  apply hne
  apply eq_target_of_zero_off_support K v x hv hx
  intro i hvi
  have hn : ¬ 0 < x i := fun hp => hnone ⟨i, hvi, hp⟩
  exact le_antisymm (le_of_not_gt hn) (hx.2 i)

/-- Phase equality is enough for strictly positive denominators on every live
nonbasic coordinate. No componentwise reference-order hypothesis is needed. -/
theorem reference_positive_of_live {n : ℕ}
    (M : ℝ) (v r x : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hphase : phaseProgressSet M v r = phaseProgressSet M v x)
    (i : Fin n) (hvi : v i = 0) (hxi : 0 < x i) : 0 < r i := by
  have hri : r i ≠ 0 := by
    intro hz
    have hxz := (same_phase_zero_iff M v r x hphase i hvi).1 hz
    linarith
  rcases lt_or_eq_of_le (hr i) with hp | he
  · exact hp
  · exact (hri he.symm).elim

theorem referencePotential_pos_of_ne_target {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (M : ℝ) (v r x : Fin n → ℝ)
    (hv : v ∈ Set.extremePoints ℝ (StandardSlice K v))
    (hr : ∀ i, 0 ≤ r i) (hx : x ∈ StandardSlice K v)
    (hphase : phaseProgressSet M v r = phaseProgressSet M v x)
    (hne : x ≠ v) : 0 < referencePotential v r x := by
  obtain ⟨i, hvi, hxi⟩ := exists_live_target_zero K v x hv hx hne
  have hri := reference_positive_of_live M v r x hr hphase i hvi hxi
  have hratio : 0 < x i / r i := div_pos hxi hri
  exact hratio.trans_le (referencePotential_ratio_le v r x hr hx.2 i hvi)

/-- A linear functional commutes with the finite list representation used by
the already checked conformal decomposition. -/
theorem circuit_linearMap_list_sum {n : ℕ}
    (f : (Fin n → ℝ) →ₗ[ℝ] ℝ) (gs : List (Fin n → ℝ)) :
    (gs.map f).sum = f gs.sum := by
  induction gs with
  | nil => simp
  | cons g gs ih => simp only [List.map_cons, List.sum_cons, map_add, ih]

theorem circuit_list_sum_neg_coordinate {n : ℕ}
    (gs : List (Fin n → ℝ)) (i : Fin n) :
    (gs.map (fun g => -g i)).sum = -gs.sum i := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
      simp only [List.map_cons, List.sum_cons, Pi.add_apply, ih]
      ring

/-- A genuine maximal norm-reduction step. The selected elementary vector
comes from the finite conformal decomposition; its maximal multiplier lies
between 1 and M. It preserves permanent progress and contracts the reference
potential by 1-1/M. There is no small/large-potential precondition. -/
theorem exists_weighted_norm_step {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (M : ℕ) (v r x : Fin n → ℝ)
    (hM : 2 ≤ M) (hnM : n ≤ M)
    (hv : v ∈ Set.extremePoints ℝ (StandardSlice K v))
    (hr : ∀ i, 0 ≤ r i) (hx : x ∈ StandardSlice K v)
    (hphase : phaseProgressSet (M : ℝ) v r = phaseProgressSet (M : ℝ) v x)
    (hne : x ≠ v) :
    ∃ y : Fin n → ℝ,
      StandardCircuitStep K v x y ∧
      phaseProgressSet (M : ℝ) v x ⊆ phaseProgressSet (M : ℝ) v y ∧
      (∀ i, v i = 0 → y i ≤ x i) ∧
      referencePotential v r y ≤
        (1 - 1 / (M : ℝ)) * referencePotential v r x := by
  classical
  have hMnat : 0 < M := by omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMnat
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  let F := referencePotential v r
  have hW : 0 < F x :=
    referencePotential_pos_of_ne_target K (M : ℝ) v r x hv hr hx hphase hne
  have hzK : v - x ∈ K := by
    simpa only [neg_sub] using K.neg_mem hx.1
  obtain ⟨gs, hlen, hall, hsumg⟩ :=
    exists_elementary_conformal_decomposition_le_n K (v - x) hzK
  have hsum : (gs.map (-F)).sum = F x := by
    rw [circuit_linearMap_list_sum, hsumg]
    change -F (v - x) = F x
    rw [map_sub, show F v = 0 from referencePotential_target v r]
    ring
  obtain ⟨g, hgmem, hscore⟩ :=
    exists_mem_ge_average gs (-F) M (F x) hMnat (hlen.trans hnM) hW hsum
  change F x / (M : ℝ) ≤ -F g at hscore
  obtain ⟨hgelem, hgconf⟩ := hall g hgmem
  have hS : 0 < -F g := (div_pos hW hMR).trans_le hscore
  have hneg : ∃ i, g i < 0 := by
    by_contra hnone
    push Not at hnone
    have hnonneg := referencePotential_nonneg v r g hr hnone
    change 0 ≤ F g at hnonneg
    linarith
  have hzero : ∀ i, x i = 0 → 0 ≤ g i := by
    intro i hxi
    apply conformalTo_coord_nonneg_of_right_nonneg hgconf
    change 0 ≤ v i - x i
    rw [hxi, sub_zero]
    exact hv.1.2 i
  obtain ⟨alpha, ha, hfeas, hsat, hmax⟩ :=
    exists_positive_maximal_nonnegative_step x g hx.2 hzero hneg
  have ha0 : 0 ≤ alpha := le_of_lt ha
  have ha1 : 1 ≤ alpha := by
    by_contra hn
    obtain ⟨i, hi⟩ := hmax 1 (lt_of_not_ge hn)
    have hunit := conformal_piece_feasible_at_one x v g hx.2 hv.1.2 hgconf i
    simp only [one_mul] at hi
    linarith
  have hy : ∀ i, 0 ≤ (x + alpha • g) i := by
    intro i
    exact hfeas i
  have hFy : 0 ≤ F (x + alpha • g) :=
    referencePotential_nonneg v r (x + alpha • g) hr hy
  have hlinear : F (x + alpha • g) = F x + alpha * F g := by
    simp only [map_add, map_smul, smul_eq_mul]
  have hscoreM : F x ≤ (-F g) * (M : ℝ) :=
    (div_le_iff₀ hMR).mp hscore
  have haM : alpha ≤ (M : ℝ) := by
    by_contra hn
    have hmul := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hS
    rw [hlinear] at hFy
    nlinarith only [hFy, hscoreM, hmul]
  have hstep := standardCircuitStep_of_maximal_direction
    K v x g alpha hx hgelem ha hfeas hmax
  have hnonbasic : ∀ i, v i = 0 → (x + alpha • g) i ≤ x i := by
    intro i hvi
    have hgi : g i ≤ 0 := conformalTo_coord_nonpos_of_right_nonpos hgconf
      (show (v - x) i ≤ 0 by change v i - x i ≤ 0; rw [hvi]; linarith [hx.2 i])
    change x i + alpha * g i ≤ x i
    have hprod := mul_nonpos_of_nonneg_of_nonpos ha0 hgi
    linarith
  have hmono : phaseProgressSet (M : ℝ) v x ⊆
      phaseProgressSet (M : ℝ) v (x + alpha • g) := by
    apply phaseProgressSet_mono
    · intro i hvi hxi
      have hle := hnonbasic i hvi
      have hge := hy i
      rw [hxi] at hle
      exact le_antisymm hle hge
    · intro i _ htrap
      exact norm_step_preserves_trapped x v g hgconf (M : ℝ) alpha
        hMone ha0 haM i (hx.2 i) htrap
  refine ⟨x + alpha • g, hstep, hmono, hnonbasic, ?_⟩
  change F (x + alpha • g) ≤ (1 - 1 / (M : ℝ)) * F x
  rw [hlinear]
  have hprod := mul_le_mul_of_nonneg_right ha1 (le_of_lt hS)
  have hid : (1 - 1 / (M : ℝ)) * F x = F x - F x / (M : ℝ) := by ring
  rw [hid]
  nlinarith only [hprod, hscore]

#print axioms referencePotential_pos_of_ne_target
#print axioms exists_weighted_norm_step

end HirschCircuit
