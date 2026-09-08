import Solutions.CircuitEliminationInvariant

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace HirschCircuit

/-- One block of `M` multiplicative contractions by `1-1/M` loses at least a
factor two. This is a rational Bernoulli/binomial estimate, not a logarithmic
argument. -/
theorem contraction_block_half (M : ℕ) (hM : 2 ≤ M) :
    ((1 - 1 / (M : ℝ)) ^ M) ≤ (1 / 2 : ℝ) := by
  have hMr : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
  let q : ℝ := 1 - 1 / (M : ℝ)
  let p : ℝ := 1 + 1 / (M : ℝ)
  have hinv0 : 0 ≤ 1 / (M : ℝ) := le_of_lt (one_div_pos.mpr hMpos)
  have hinv1 : 1 / (M : ℝ) ≤ 1 := by
    exact (div_le_one hMpos).2 (by linarith)
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hp0 : 0 ≤ p := by dsimp [p]; linarith
  have hp2 : (2 : ℝ) ≤ p ^ M := by
    have hbern := one_add_mul_le_pow (a := 1 / (M : ℝ)) (by linarith) M
    have hcast : (M : ℝ) * (1 / (M : ℝ)) = 1 := by field_simp [hMne]
    dsimp [p]
    rw [hcast] at hbern
    norm_num at hbern ⊢
    exact hbern
  have hqp0 : 0 ≤ q * p := mul_nonneg hq0 hp0
  have hqp1 : q * p ≤ 1 := by
    dsimp [q, p]
    have hs : 0 ≤ (1 / (M : ℝ)) ^ 2 := sq_nonneg _
    nlinarith
  have hpow : (q * p) ^ M ≤ (1 : ℝ) ^ M :=
    pow_le_pow_left₀ hqp0 hqp1 M
  rw [mul_pow, one_pow] at hpow
  have hqpow0 : 0 ≤ q ^ M := pow_nonneg hq0 _
  have hmul : 2 * q ^ M ≤ q ^ M * p ^ M := by
    simpa [mul_comm] using (mul_le_mul_of_nonneg_left hp2 hqpow0)
  have hqhalf : q ^ M ≤ (1 / 2 : ℝ) := by
    nlinarith only [hmul, hpow]
  simpa [q] using hqhalf

/-- A purely natural-number exponential envelope used after taking `4*M`
contraction blocks. -/
theorem two_mul_cube_le_two_pow_four_mul (M : ℕ) (hM : 1 ≤ M) :
    2 * M ^ 3 ≤ 2 ^ (4 * M) := by
  have hsqp1 := Nat.two_mul_sq_add_one_le_two_pow_two_mul M
  have hsq : 2 * M ^ 2 ≤ 2 ^ (2 * M) := by omega
  have hMle : M ≤ 2 * M ^ 2 := by nlinarith
  have hMpow : M ≤ 2 ^ (2 * M) := hMle.trans hsq
  have hmul := Nat.mul_le_mul hsq hMpow
  calc
    2 * M ^ 3 = (2 * M ^ 2) * M := by ring
    _ ≤ (2 ^ (2 * M)) * (2 ^ (2 * M)) := hmul
    _ = 2 ^ (4 * M) := by rw [← pow_add]; congr 1 <;> ring

/-- After `4*M^2` norm contractions, an initial potential at most `M` is at
most `1/(2*M^2)`, the elimination threshold used by the support-safe proof. -/
theorem contraction_to_elimination_threshold (M : ℕ) (hM : 2 ≤ M) :
    (M : ℝ) * (1 - 1 / (M : ℝ)) ^ (4 * M ^ 2) ≤
      1 / (2 * (M : ℝ) ^ 2) := by
  have hblock := contraction_block_half M hM
  have hM1 : 1 ≤ M := by omega
  have hMr : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hq0 : 0 ≤ (1 - 1 / (M : ℝ)) := by
    have hinv1 : 1 / (M : ℝ) ≤ 1 := (div_le_one hMr).2 (by exact_mod_cast hM1)
    linarith
  have hpow0 : 0 ≤ (1 - 1 / (M : ℝ)) ^ M := pow_nonneg hq0 _
  have hpow :
      ((1 - 1 / (M : ℝ)) ^ M) ^ (4 * M) ≤
        ((1 / 2 : ℝ)) ^ (4 * M) :=
    pow_le_pow_left₀ hpow0 hblock (4 * M)
  have hexp : M * (4 * M) = 4 * M ^ 2 := by ring
  rw [← pow_mul, hexp] at hpow
  have hnat := two_mul_cube_le_two_pow_four_mul M hM1
  have hnatR : (2 : ℝ) * (M : ℝ) ^ 3 ≤ (2 : ℝ) ^ (4 * M) := by
    exact_mod_cast hnat
  have htwo : (0 : ℝ) < (2 : ℝ) ^ (4 * M) := pow_pos (by norm_num) _
  have hden : (0 : ℝ) < 2 * (M : ℝ) ^ 2 := by positivity
  have hfrac : (M : ℝ) * (1 / 2 : ℝ) ^ (4 * M) ≤
      1 / (2 * (M : ℝ) ^ 2) := by
    rw [one_div_pow]
    have heq :
        (M : ℝ) * (1 * ((2 : ℝ) ^ (4 * M))⁻¹) =
          (M : ℝ) / (2 : ℝ) ^ (4 * M) := by
      simp [div_eq_mul_inv]
    rw [heq]
    apply (div_le_div_iff₀ htwo hden).2
    nlinarith only [hnatR]
  exact (mul_le_mul_of_nonneg_left hpow (by positivity)).trans hfrac

#print axioms contraction_block_half
#print axioms two_mul_cube_le_two_pow_four_mul
#print axioms contraction_to_elimination_threshold

end HirschCircuit
