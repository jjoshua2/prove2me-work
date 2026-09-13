import Mathlib
set_option autoImplicit false
noncomputable section

theorem solution (x root denominator Gamma eta : ℝ)
    (hGamma : 0 ≤ Gamma) (heta : 0 < eta) (hroot : 0 < |root|)
    (htransport : |x| ≤ Gamma * |root|)
    (hgap : eta * |root| ≤ |denominator|) :
    |x / denominator| ≤ Gamma / eta := by
  have hd : 0 < |denominator| := lt_of_lt_of_le (mul_pos heta hroot) hgap
  rw [abs_div]
  apply (div_le_div_iff₀ hd heta).mpr
  have h₁ := mul_le_mul_of_nonneg_right htransport heta.le
  have h₂ := mul_le_mul_of_nonneg_left hgap hGamma
  nlinarith

#print axioms solution
