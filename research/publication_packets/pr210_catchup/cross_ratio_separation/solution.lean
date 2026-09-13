import Mathlib
set_option autoImplicit false
noncomputable section

theorem solution (s t u v delta epsilon : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hu1 : u ≤ 1) (hv1 : v ≤ 1) (hdelta : 0 ≤ delta) (hepsilon : 0 ≤ epsilon)
    (hdelta_s : delta ≤ s) (hdelta_t : delta ≤ t)
    (heq : s * t = epsilon * u * v) : delta ^ 2 ≤ epsilon := by
  have hl : delta ^ 2 ≤ s * t := by
    calc
      delta ^ 2 = delta * delta := by ring
      _ ≤ s * delta := mul_le_mul_of_nonneg_right hdelta_s hdelta
      _ ≤ s * t := mul_le_mul_of_nonneg_left hdelta_t hs
  have huv : u * v ≤ 1 := by
    calc
      u * v ≤ 1 * v := mul_le_mul_of_nonneg_right hu1 hv
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hv1 (by norm_num : (0 : ℝ) ≤ 1)
      _ = 1 := by ring
  have hr := mul_le_mul_of_nonneg_left huv hepsilon
  nlinarith

#print axioms solution
