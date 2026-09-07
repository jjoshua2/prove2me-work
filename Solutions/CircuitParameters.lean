import Mathlib

set_option maxHeartbeats 4000000

namespace HirschCircuitParameters

/-- A deliberately conservative rational choice for the ghost-point
parameters. It is independent of all numerical data of the polyhedron. -/
theorem elimination_parameters
    (M rho : ℝ) (hM : 2 ≤ M) (hr0 : 0 ≤ rho)
    (hr : rho ≤ 1 / (8 * M ^ 3)) :
    let lambda := 1 / (4 * M ^ 2)
    let eta := (1 - lambda) * rho / (1 - rho)
    0 < lambda ∧ 0 ≤ eta ∧ eta * M ≤ lambda / 2 ∧
      (lambda + eta) * M ^ 2 ≤ 5 / 16 ∧ rho < 1 := by
  dsimp
  have hMpos : 0 < M := by linarith
  have hM2 : 0 < M ^ 2 := by positivity
  have hM3 : 0 < M ^ 3 := by positivity
  have hMsq : 4 ≤ M ^ 2 := by nlinarith
  have hMcube : 8 ≤ M ^ 3 := by
    have hprod : (2 : ℝ) * 4 ≤ M * M ^ 2 :=
      mul_le_mul hM hMsq (by norm_num) hMpos.le
    nlinarith
  have htau : 1 / (8 * M ^ 3) ≤ 1 / 64 := by
    apply (div_le_iff₀ (by positivity : 0 < 8 * M ^ 3)).2
    nlinarith
  have hr1 : rho < 1 := by linarith
  have hd : 0 < 1 - rho := by linarith
  have hlam : 0 < 1 / (4 * M ^ 2) := by positivity
  have hlam1 : 1 / (4 * M ^ 2) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * M ^ 2)).2
    nlinarith
  have htaulam : 1 / (8 * M ^ 3) ≤ 1 / (4 * M ^ 2) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 8 * M ^ 3)
      (by positivity : 0 < 4 * M ^ 2)).2
    have hprod : 0 ≤ (2 * M - 1) * M ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg M)
    nlinarith
  have hrlam : rho ≤ 1 / (4 * M ^ 2) := hr.trans htaulam
  have he0 : 0 ≤ (1 - 1 / (4 * M ^ 2)) * rho / (1 - rho) := by
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr hlam1) hr0) hd.le
  have herho : (1 - 1 / (4 * M ^ 2)) * rho / (1 - rho) ≤ rho := by
    apply (div_le_iff₀ hd).2
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hrlam)]
  have hprotect : (1 - 1 / (4 * M ^ 2)) * rho / (1 - rho) * M ≤
      (1 / (4 * M ^ 2)) / 2 := by
    have h1 := mul_le_mul_of_nonneg_right (herho.trans hr) hMpos.le
    have heq : (1 / (8 * M ^ 3)) * M = (1 / (4 * M ^ 2)) / 2 := by
      field_simp [hMpos.ne'] <;> ring
    exact h1.trans_eq heq
  have hsmall : (1 / (4 * M ^ 2) +
      (1 - 1 / (4 * M ^ 2)) * rho / (1 - rho)) * M ^ 2 ≤ 5 / 16 := by
    have h1 := mul_le_mul_of_nonneg_right
      (add_le_add_left (herho.trans hr) (1 / (4 * M ^ 2))) hM2.le
    have heq : (1 / (4 * M ^ 2) + 1 / (8 * M ^ 3)) * M ^ 2 =
        1 / 4 + 1 / (8 * M) := by
      field_simp [hMpos.ne'] <;> ring
    rw [heq] at h1
    have hlast : 1 / (8 * M) ≤ 1 / 16 := by
      apply (div_le_iff₀ (by positivity : 0 < 8 * M)).2
      linarith
    linarith
  exact ⟨hlam, he0, hprotect, hsmall, hr1⟩

#print axioms elimination_parameters

end HirschCircuitParameters
