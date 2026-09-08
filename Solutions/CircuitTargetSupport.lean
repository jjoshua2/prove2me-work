import Solutions.CircuitSourceBridge

set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set

namespace HirschCircuit

/-- In the nonnegative affine slice through an extreme target `v`, a feasible
point that vanishes everywhere outside the positive support of `v` is `v`.
This is the target-support uniqueness fact used by the support-safe routing
argument. -/
theorem eq_target_of_zero_off_support {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ))
    (v y : Fin n → ℝ)
    (hv : v ∈ extremePoints ℝ (StandardSlice K v))
    (hy : y ∈ StandardSlice K v)
    (hsupp : ∀ i, v i = 0 → y i = 0) :
    y = v := by
  by_contra hne
  let h : Fin n → ℝ := y - v
  have hh0 : h ≠ 0 := by
    intro hz
    apply hne
    funext i
    have hi := congrFun hz i
    dsimp [h] at hi
    linarith
  have hhK : h ∈ K := by
    simpa [h] using hy.1
  have hvFeas : v ∈ StandardSlice K v := extremePoints_subset hv
  have hvNonneg : ∀ i, 0 ≤ v i := hvFeas.2
  have hyNonneg : ∀ i, 0 ≤ y i := hy.2

  let D : Finset (Fin n) := Finset.univ.filter (fun i => 0 < h i)
  obtain ⟨eps, heps, hback⟩ : ∃ eps : ℝ, 0 < eps ∧
      ∀ i, 0 ≤ v i - eps * h i := by
    by_cases hD : D.Nonempty
    · obtain ⟨q, hqD, hmin⟩ :=
        D.exists_min_image (fun i => v i / h i) hD
      have hqpos : 0 < h q := (Finset.mem_filter.mp hqD).2
      have hvqpos : 0 < v q := by
        have hvq := hvNonneg q
        by_contra hnot
        have hvq0 : v q = 0 := le_antisymm (le_of_not_gt hnot) hvq
        have hyq0 := hsupp q hvq0
        dsimp [h] at hqpos
        linarith
      let eps : ℝ := v q / h q
      have heps : 0 < eps := div_pos hvqpos hqpos
      refine ⟨eps, heps, ?_⟩
      intro i
      by_cases hi : 0 < h i
      · have hiD : i ∈ D := by simp [D, hi]
        have hle : eps ≤ v i / h i := by
          simpa [eps] using hmin i hiD
        have hmul := (le_div_iff₀ hi).mp hle
        linarith
      · have hhi : h i ≤ 0 := le_of_not_gt hi
        have hmul : eps * h i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt heps) hhi
        linarith [hvNonneg i]
    · refine ⟨1, zero_lt_one, ?_⟩
      intro i
      have hiNot : i ∉ D := by
        intro hiD
        exact hD ⟨i, hiD⟩
      have hhi : h i ≤ 0 := by
        have : ¬ 0 < h i := by simpa [D] using hiNot
        exact le_of_not_gt this
      linarith [hvNonneg i]

  let w : Fin n → ℝ := v - eps • h
  have hwK : w - v ∈ K := by
    have heq : w - v = (-eps) • h := by
      funext i
      simp only [w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact K.smul_mem _ hhK
  have hwNonneg : ∀ i, 0 ≤ w i := by
    intro i
    simpa [w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using hback i
  have hw : w ∈ StandardSlice K v := ⟨hwK, hwNonneg⟩

  have hseg : v ∈ openSegment ℝ y w := by
    rw [mem_openSegment_iff_div]
    refine ⟨eps, 1, heps, zero_lt_one, ?_⟩
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w, h, Pi.sub_apply]
    have hden : eps + 1 ≠ 0 := ne_of_gt (by linarith : 0 < eps + 1)
    field_simp [hden]
    ring

  rw [mem_extremePoints] at hv
  have hyv := (hv.2 y hy w hw hseg).1
  exact hne hyv

#print axioms eq_target_of_zero_off_support

end HirschCircuit
