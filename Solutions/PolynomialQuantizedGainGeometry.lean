import Mathlib

/-!
# Exact cycle-gain certificates beyond magnitude balance

A real potential change does not change a closed-walk exponent sum. A negative
cycle therefore certifies that no coordinate gauge can meet the proposed
smaller radius. Nontrivial integer powers of q>1 stay a definite distance from
one. These are the finite/algebraic cores of the companion all-basis inverse
argument; its graph extraction and the external normal-cone diameter theorem
are not silently claimed formalized here.

NEW UNCOMPILED candidates. No Lean or platform acceptance is asserted.
-/
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace HirschGainLattice

theorem sum_potential_difference (p : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (p i-p (i+1))) = p 0-p n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    ring

/-- This lower-bound certificate rules out real gauges, not merely integer
potentials tried by the Bellman--Ford implementation. -/
theorem closed_walk_gain_invariant (w p : ℕ → ℝ) (n : ℕ)
    (hclosed : p n=p 0) :
    (∑ i ∈ Finset.range n, (w i+p i-p (i+1))) = ∑ i ∈ Finset.range n,w i := by
  calc
    (∑ i ∈ Finset.range n, (w i+p i-p (i+1))) =
        (∑ i ∈ Finset.range n,w i) + ∑ i ∈ Finset.range n,(p i-p (i+1)) := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i ∈ Finset.range n,w i := by rw [sum_potential_difference,hclosed];ring

theorem negative_cycle_forbids_radius (w p : ℕ → ℝ) (n : ℕ) (K : ℝ)
    (hclosed : p n=p 0) (hnegative : (∑ i ∈ Finset.range n,(w i+K))<0) :
    ¬ (∀ i<n, -K≤w i+p i-p (i+1)) := by
  intro h
  have hs : 0≤∑ i ∈ Finset.range n,((w i+K)+p i-p (i+1)) := by
    apply Finset.sum_nonneg
    intro i hi
    have hloc := h i (Finset.mem_range.mp hi)
    linarith
  rw [closed_walk_gain_invariant (fun i => w i+K) p n hclosed] at hs
  linarith

lemma base_le_positive_power (q : ℝ) (hq : 1≤q) (k : ℕ) : q≤q^(k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : 0≤q^(k+1) := pow_nonneg (by linarith) _
    calc
      q ≤ q^(k+1) := ih
      _ = q^(k+1)*1 := by ring
      _ ≤ q^(k+1)*q := mul_le_mul_of_nonneg_left hq hp
      _ = q^(k+1+1) := by
        exact (pow_succ q (k+1)).symm

lemma inverse_le_one_of_base (q : ℝ) (hq : 1<q) : q⁻¹≤1 := by
  have hp : 0<q := by linarith
  have h := mul_le_mul_of_nonneg_right hq.le (inv_nonneg.mpr hp.le)
  simpa [mul_inv_cancel₀ (ne_of_gt hp)] using h

/-- The gap 1-q^-1 also applies to positive powers, whose gap is actually larger. -/
theorem positive_power_gap (q : ℝ) (hq : 1<q) (k : ℕ) :
    1-q⁻¹≤|1-q^(k+1)| := by
  have hp := base_le_positive_power q hq.le k
  have hi := inverse_le_one_of_base q hq
  have hqpos : 0<q := by linarith
  have he : q*q⁻¹=1 := mul_inv_cancel₀ (ne_of_gt hqpos)
  have hprod := mul_nonneg (sub_nonneg.mpr hq.le) (sub_nonneg.mpr hi)
  rw [abs_of_nonpos (by linarith : 1-q^(k+1)≤0)]
  nlinarith

theorem reciprocal_power_gap (q : ℝ) (hq : 1<q) (k : ℕ) :
    1-q⁻¹≤|1-(q^(k+1))⁻¹| := by
  have hp := base_le_positive_power q hq.le k
  have hqpos : 0<q := by linarith
  have hrpos : 0<q^(k+1) := lt_of_lt_of_le hqpos hp
  have hi : (q^(k+1))⁻¹≤q⁻¹ := (inv_le_inv₀ hrpos hqpos).2 hp
  have htop := inverse_le_one_of_base q hq
  rw [abs_of_nonneg (by linarith : 0≤1-(q^(k+1))⁻¹)]
  linarith

/-- A sign-negative cycle cannot nearly cancel, even with arbitrary positive
magnitude. It is positive cycles near magnitude one that require a gap. -/
theorem negative_sign_cycle_gap (q x : ℝ) (hq : 0<q) (hx : 0≤x) :
    1-q⁻¹≤|1-(-x)| := by
  rw [abs_of_nonneg (by linarith : 0≤1-(-x))]
  have hi : 0≤q⁻¹ := inv_nonneg.mpr hq.le
  linarith

/-- Normalize a deleted-row kernel column. The root-ratio and cycle-gap
premises are supplied by the concrete graph proof, not by a determinant bound. -/
theorem normalized_column_bound (x root denominator Γ η : ℝ)
    (hΓ : 0≤Γ) (hη : 0<η) (hroot : 0 < |root|)
    (htransport : |x| ≤ Γ*|root|) (hgap : η*|root| ≤ |denominator|) :
    |x/denominator|≤Γ/η := by
  have hd : 0<|denominator| := lt_of_lt_of_le (mul_pos hη hroot) hgap
  rw [abs_div]
  apply (div_le_div_iff₀ hd hη).mpr
  have h₁ := mul_le_mul_of_nonneg_right htransport hη.le
  have h₂ := mul_le_mul_of_nonneg_left hgap hΓ
  nlinarith

#print axioms sum_potential_difference
#print axioms closed_walk_gain_invariant
#print axioms negative_cycle_forbids_radius
#print axioms positive_power_gap
#print axioms reciprocal_power_gap
#print axioms negative_sign_cycle_gap
#print axioms normalized_column_bound
end HirschGainLattice
