import Mathlib
import Solutions.PolynomialExcessTwoMomentSlice

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 3000000
set_option autoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschExcessTwo

/-- A feasible point of the normalized moment slice whose support is contained
in a low/high pair is the explicit `pairPoint` on that pair. -/
theorem eq_pairPoint_of_mem_of_zero_off_pair {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j : Fin n)
    (hli : t i < mu) (hrj : mu < t j)
    (s : EuclideanSpace ℝ (Fin n)) (hs : s ∈ momentSlice t mu)
    (hzero : ∀ k, k ≠ i → k ≠ j → s k = 0) :
    s = pairPoint t mu i j := by
  classical
  have hij : i ≠ j := by
    intro h
    subst j
    linarith
  have hden : 0 < t j - t i := by linarith
  have hmassSum := sum_eq_add_of_zero_off_pair (fun k => s k) i j hij hzero
  have hmass : s i + s j = 1 := by
    calc
      s i + s j = ∑ k, s k := hmassSum.symm
      _ = 1 := hs.2.1
  have hmomSum := sum_eq_add_of_zero_off_pair
    (fun k => t k * s k) i j hij (by
      intro k hki hkj
      rw [hzero k hki hkj, mul_zero])
  have hmom : t i * s i + t j * s j = mu := by
    calc
      t i * s i + t j * s j = ∑ k, t k * s k := hmomSum.symm
      _ = mu := hs.2.2
  have hsi : s i = (t j - mu) / (t j - t i) := by
    apply (eq_div_iff (ne_of_gt hden)).2
    nlinarith [hmass, hmom]
  have hsj : s j = (mu - t i) / (t j - t i) := by
    apply (eq_div_iff (ne_of_gt hden)).2
    nlinarith [hmass, hmom]
  ext k
  by_cases hki : k = i
  · subst k
    change s i = pairPoint t mu i j i
    rw [hsi, pairPoint_apply_left]
  · by_cases hkj : k = j
    · subst k
      change s j = pairPoint t mu i j j
      rw [hsj, pairPoint_apply_right t mu i j hij]
    · change s k = pairPoint t mu i j k
      rw [hzero k hki hkj, pairPoint_apply_other t mu i j k hki hkj]

/-- Every low/high two-support point is an actual extreme vertex of the
normalized moment slice. The proof uses only coordinate-zero extreme faces
and the two moment equations; no global vertex enumeration is used. -/
theorem pairPoint_mem_extremePoints {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j : Fin n)
    (hli : t i < mu) (hrj : mu < t j) :
    pairPoint t mu i j ∈ extremePoints ℝ (momentSlice t mu) := by
  classical
  have hij : i ≠ j := by
    intro h
    subst j
    linarith
  have hp : pairPoint t mu i j ∈ momentSlice t mu := pairPoint_mem t mu i j hli hrj
  rw [mem_extremePoints_iff_left]
  refine ⟨hp, ?_⟩
  intro x hx y hy hseg
  apply eq_pairPoint_of_mem_of_zero_off_pair t mu i j hli hrj x hx
  intro k hki hkj
  have hpzero : pairPoint t mu i j ∈ zeroFace t mu k := by
    exact ⟨hp, pairPoint_apply_other t mu i j k hki hkj⟩
  have hxzero := (zeroFace_isExtreme t mu k).left_mem_of_mem_openSegment hx hy hpzero hseg
  exact hxzero.2

#print axioms eq_pairPoint_of_mem_of_zero_off_pair
#print axioms pairPoint_mem_extremePoints

end HirschExcessTwo
