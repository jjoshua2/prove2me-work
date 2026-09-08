import Solutions.CircuitConformalBasics

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Hirsch

namespace HirschCircuit

/-- A strictly positive maximal augmentation exists when the direction is
nonnegative at every currently zero coordinate and has some negative entry. -/
theorem exists_positive_maximal_nonnegative_step {n : ℕ}
    (x g : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hzero : ∀ i, x i = 0 → 0 ≤ g i)
    (hneg : ∃ i, g i < 0) :
    ∃ α : ℝ, 0 < α ∧ (∀ i, 0 ≤ x i + α * g i) ∧
      (∃ q, g q < 0 ∧ x q + α * g q = 0) ∧
      ∀ β : ℝ, α < β → ∃ i, x i + β * g i < 0 := by
  classical
  let D : Finset (Fin n) := Finset.univ.filter (fun i => g i < 0)
  have hD : D.Nonempty := by
    obtain ⟨i, hi⟩ := hneg
    exact ⟨i, by simp [D, hi]⟩
  obtain ⟨q, hqD, hmin⟩ := D.exists_min_image (fun i => x i / (-g i)) hD
  have hq : g q < 0 := (Finset.mem_filter.mp hqD).2
  have hxq : 0 < x q := by
    have hn := hx q
    by_contra hh
    have hz : x q = 0 := le_antisymm (le_of_not_gt hh) hn
    have := hzero q hz
    linarith
  let α : ℝ := x q / (-g q)
  have hα : 0 < α := div_pos hxq (neg_pos.mpr hq)
  have hsat : x q + α * g q = 0 := by
    have he : α * (-g q) = x q := div_mul_cancel₀ _ (ne_of_gt (neg_pos.mpr hq))
    nlinarith
  refine ⟨α, hα, ?_, ⟨q, hq, hsat⟩, ?_⟩
  · intro i
    by_cases hi : g i < 0
    · have hle : α ≤ x i / (-g i) := hmin i (by simp [D, hi])
      have hmul := (le_div_iff₀ (neg_pos.mpr hi)).mp hle
      nlinarith
    · exact add_nonneg (hx i) (mul_nonneg (le_of_lt hα) (le_of_not_gt hi))
  · intro β hβ
    refine ⟨q, ?_⟩
    have := mul_lt_mul_of_pos_right hβ (neg_pos.mpr hq)
    nlinarith

/-- Every conformal piece of v-x is feasible for step length one. -/
theorem conformal_piece_feasible_at_one {n : ℕ}
    (x v g : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (hv : ∀ i, 0 ≤ v i)
    (hg : ConformalTo g (v - x)) : ∀ i, 0 ≤ x i + g i := by
  intro i
  by_cases hi : x i ≤ v i
  · have hgi : 0 ≤ g i := conformalTo_coord_nonneg_of_right_nonneg hg
      (show 0 ≤ (v - x) i by change 0 ≤ v i - x i; linarith)
    linarith [hx i]
  · have hvi : v i ≤ x i := le_of_lt (lt_of_not_ge hi)
    have hgi : g i ≤ 0 := conformalTo_coord_nonpos_of_right_nonpos hg
      (show (v - x) i ≤ 0 by change v i - x i ≤ 0; linarith)
    have habs := (hg i).2
    change |g i| ≤ |v i - x i| at habs
    rw [abs_of_nonpos hgi, abs_of_nonpos (sub_nonpos.mpr hvi)] at habs
    linarith [hv i]

/-- Norm-step trapped-coordinate preservation, parametrized by the circuit-count bound. -/
theorem norm_step_preserves_trapped {n : ℕ}
    (x v g : Fin n → ℝ) (hg : ConformalTo g (v - x))
    (M α : ℝ) (hM : 1 ≤ M) (hα0 : 0 ≤ α) (hαM : α ≤ M)
    (i : Fin n) (hxi : 0 ≤ x i) (htrap : x i ≤ M * v i) :
    x i + α * g i ≤ M * v i := by
  by_cases hi : v i ≤ x i
  · have hgi : g i ≤ 0 := conformalTo_coord_nonpos_of_right_nonpos hg
      (show (v - x) i ≤ 0 by change v i - x i ≤ 0; linarith)
    have := mul_nonpos_of_nonneg_of_nonpos hα0 hgi
    linarith
  · have hvi : x i ≤ v i := le_of_lt (lt_of_not_ge hi)
    have hgi : 0 ≤ g i := conformalTo_coord_nonneg_of_right_nonneg hg
      (show 0 ≤ (v - x) i by change 0 ≤ v i - x i; linarith)
    have habs := (hg i).2
    change |g i| ≤ |v i - x i| at habs
    rw [abs_of_nonneg hgi, abs_of_nonneg (sub_nonneg.mpr hvi)] at habs
    have h1 := mul_le_mul_of_nonneg_left habs hα0
    have h2 := mul_le_mul_of_nonneg_right hαM (sub_nonneg.mpr hvi)
    nlinarith

/-- The zero-support invariant required by the source elimination step. -/
theorem elimination_piece_zero_of_reference_zero {n : ℕ}
    (x r v g : Fin n → ℝ) (ρ λ : ℝ)
    (hg : ConformalTo g
      ((x + (ρ / (1 - ρ)) • (x - r) +
        λ • (v - (x + (ρ / (1 - ρ)) • (x - r)))) - x))
    (i : Fin n) (hx : x i = 0) (hr : r i = 0) (hv : v i = 0) :
    g i = 0 := by
  apply conformalTo_eq_zero_of_right_eq_zero hg
  simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, hx, hr, hv]

/-- Quantitative protection of any zero coordinate. The reference-bound
hypothesis follows from trapped-set preservation or from resetting on support loss. -/
theorem elimination_direction_nonnegative_at_zero {n : ℕ}
    (x r v g : Fin n → ℝ) (M λ γ : ℝ)
    (hv : ∀ i, 0 ≤ v i) (hγ : 0 ≤ γ) (hsmall : γ * M ≤ λ)
    (hg : ConformalTo g (λ • (v - x) + γ • (x - r)))
    (href : ∀ i, x i = 0 → r i ≤ M * v i) :
    ∀ i, x i = 0 → 0 ≤ g i := by
  intro i hi
  apply conformalTo_coord_nonneg_of_right_nonneg hg
  change 0 ≤ λ * (v i - x i) + γ * (x i - r i)
  rw [hi]
  have h1 := mul_le_mul_of_nonneg_left (href i hi) hγ
  have h2 := mul_le_mul_of_nonneg_right hsmall (hv i)
  nlinarith

/-- An outward direction at zero rules out every positive feasible step. -/
theorem no_positive_step_of_negative_at_zero {n : ℕ}
    (x g : Fin n → ℝ) (i : Fin n) (hx : x i = 0) (hg : g i < 0) :
    ∀ α : ℝ, 0 < α → ¬ (∀ j, 0 ≤ x j + α * g j) := by
  intro α hα hfeas
  have hi := hfeas i
  rw [hx, zero_add] at hi
  exact (not_le_of_gt (mul_neg_of_pos_of_neg hα hg)) hi

#print axioms exists_positive_maximal_nonnegative_step
#print axioms conformal_piece_feasible_at_one
#print axioms norm_step_preserves_trapped
#print axioms elimination_piece_zero_of_reference_zero
#print axioms elimination_direction_nonnegative_at_zero
#print axioms no_positive_step_of_negative_at_zero
end HirschCircuit
