import Solutions.CircuitConformalBasics

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators

namespace HirschCircuit

/-- Finite support of a coordinate vector. -/
noncomputable def supportFinset {n : ℕ} (x : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ≠ 0)

@[simp] theorem mem_supportFinset {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    i ∈ supportFinset x ↔ x i ≠ 0 := by
  simp [supportFinset]

/-- A half-scaled perturbation stays conformal when the perturbation is no
larger coordinatewise than the original conformal vector. -/
theorem half_perturb_conformal {n : ℕ} {w z h : Fin n → ℝ} {t : ℝ}
    (hwz : ConformalTo w z)
    (hsub : Function.support h ⊆ Function.support w)
    (hpert : ∀ i, |t * h i| ≤ |w i|) :
    ConformalTo ((1 / 2 : ℝ) • (w + t • h)) z := by
  intro i
  have habsw := (hwz i).2
  have hp := hpert i
  have hadd : |w i + t * h i| ≤ |w i| + |t * h i| := abs_add_le _ _
  have hyabs : |((1 / 2 : ℝ) * (w i + t * h i))| ≤ |w i| := by
    rw [abs_mul]
    norm_num
    nlinarith [hadd]
  constructor
  · rcases lt_trichotomy (w i) 0 with hwneg | hwzero | hwpos
    · have hznonpos : z i ≤ 0 := by
        have hs := (hwz i).1
        nlinarith
      have hupper : t * h i ≤ -w i := by
        have hself := le_abs_self (t * h i)
        rw [abs_of_neg hwneg] at hp
        linarith
      have hy : (1 / 2 : ℝ) * (w i + t * h i) ≤ 0 := by linarith
      exact mul_nonneg_of_nonpos_of_nonpos hy hznonpos
    · have hhzero : h i = 0 := by
        by_contra hh
        have hm : i ∈ Function.support h := by simpa [Function.mem_support] using hh
        have := hsub hm
        simpa [Function.mem_support, hwzero] using this
      simp [hwzero, hhzero]
    · have hznonneg : 0 ≤ z i := by
        have hs := (hwz i).1
        nlinarith
      have hlower : -w i ≤ t * h i := by
        have hself := neg_abs_le (t * h i)
        rw [abs_of_pos hwpos] at hp
        linarith
      have hy : 0 ≤ (1 / 2 : ℝ) * (w i + t * h i) := by linarith
      exact mul_nonneg hy hznonneg
  · simpa only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] using hyabs.trans habsw

/-- Every nonzero vector in a finite-dimensional subspace admits a
support-minimal elementary vector conformal to it. This is the circuit piece
existence lemma underlying conformal circuit decompositions. -/
theorem exists_elementary_conformal {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) {z : Fin n → ℝ}
    (hzK : z ∈ K) (hz0 : z ≠ 0) :
    ∃ g : Fin n → ℝ, IsElementaryIn K g ∧ ConformalTo g z := by
  classical
  let Good : (Fin n → ℝ) → Prop := fun w =>
    w ≠ 0 ∧ w ∈ K ∧ ConformalTo w z
  have hzGood : Good z := ⟨hz0, hzK, conformalTo_refl z⟩
  have hex : ∃ k : ℕ, ∃ w : Fin n → ℝ,
      (supportFinset w).card = k ∧ Good w :=
    ⟨(supportFinset z).card, z, rfl, hzGood⟩
  obtain ⟨w, hwcard, hwGood⟩ := Nat.find_spec hex
  have hmin : ∀ y : Fin n → ℝ, Good y →
      (supportFinset w).card ≤ (supportFinset y).card := by
    intro y hy
    rw [hwcard]
    exact Nat.find_min' hex ⟨y, rfl, hy⟩
  refine ⟨w, ?_, hwGood.2.2⟩
  refine ⟨hwGood.1, hwGood.2.1, ?_⟩
  intro h hh0 hhK hsub
  by_contra hnrev
  obtain ⟨k, hwk, hhk⟩ := Set.not_subset.mp hnrev
  have hwk0 : w k ≠ 0 := by simpa [Function.mem_support] using hwk
  have hhk0 : h k = 0 := by simpa [Function.mem_support] using hhk

  let D : Finset (Fin n) := Finset.univ.filter (fun i => h i ≠ 0)
  have hexh : ∃ i, h i ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hh0
    funext i
    exact hall i
  have hD : D.Nonempty := by
    obtain ⟨i, hi⟩ := hexh
    exact ⟨i, by simp [D, hi]⟩
  obtain ⟨q, hqD, hratio⟩ :=
    D.exists_min_image (fun i => |w i| / |h i|) hD
  have hhq0 : h q ≠ 0 := (Finset.mem_filter.mp hqD).2
  have hwq0 : w q ≠ 0 := by
    have hqSuppH : q ∈ Function.support h := by
      simpa [Function.mem_support] using hhq0
    have := hsub hqSuppH
    simpa [Function.mem_support] using this
  let t : ℝ := -(w q / h q)
  have hcancel : w q + t * h q = 0 := by
    dsimp [t]
    field_simp [hhq0]
    ring
  have hpert : ∀ i, |t * h i| ≤ |w i| := by
    intro i
    by_cases hhi0 : h i = 0
    · simp [hhi0]
    · have hiD : i ∈ D := by simp [D, hhi0]
      have hle := hratio i hiD
      have hmul := mul_le_mul_of_nonneg_right hle (abs_nonneg (h i))
      have habshi : |h i| ≠ 0 := abs_ne_zero.mpr hhi0
      calc
        |t * h i| = (|w q| / |h q|) * |h i| := by
          simp [t, abs_mul, abs_div]
        _ ≤ (|w i| / |h i|) * |h i| := hmul
        _ = |w i| := by field_simp [habshi]
  let y : Fin n → ℝ := (1 / 2 : ℝ) • (w + t • h)
  have hyConf : ConformalTo y z := by
    exact half_perturb_conformal hwGood.2.2 hsub hpert
  have hyK : y ∈ K := by
    exact K.smul_mem _ (K.add_mem hwGood.2.1 (K.smul_mem t hhK))
  have hy0 : y ≠ 0 := by
    intro hy
    have hyk := congrFun hy k
    simp only [y, Pi.smul_apply, Pi.add_apply, smul_eq_mul, hhk0, mul_zero, add_zero] at hyk
    norm_num at hyk
    exact hwk0 hyk
  have hySub : supportFinset y ⊆ supportFinset w := by
    intro i hi
    simp only [mem_supportFinset] at hi ⊢
    intro hwi0
    have hhi0 : h i = 0 := by
      by_contra hh
      have hm : i ∈ Function.support h := by simpa [Function.mem_support] using hh
      have := hsub hm
      simpa [Function.mem_support, hwi0] using this
    apply hi
    simp [y, hwi0, hhi0]
  have hqIn : q ∈ supportFinset w := by simp [hwq0]
  have hqOut : q ∉ supportFinset y := by
    simp only [mem_supportFinset, not_not]
    change (1 / 2 : ℝ) * (w q + t * h q) = 0
    rw [hcancel]
    ring
  have hyNe : supportFinset y ≠ supportFinset w := by
    intro heq
    have : q ∈ supportFinset y := heq.symm ▸ hqIn
    exact hqOut this
  have hstrict : supportFinset y ⊂ supportFinset w :=
    ssubset_of_ne_of_subset hyNe hySub
  have hcardlt : (supportFinset y).card < (supportFinset w).card :=
    Finset.card_lt_card hstrict
  have hcardmin := hmin y ⟨hy0, hyK, hyConf⟩
  omega

/-- Rescale an elementary conformal direction until at least one coordinate of
the residual vanishes. The scaled vector is still elementary and conformal,
and subtracting it strictly decreases support. -/
theorem exists_saturating_elementary_conformal {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) {z : Fin n → ℝ}
    (hzK : z ∈ K) (hz0 : z ≠ 0) :
    ∃ g : Fin n → ℝ,
      IsElementaryIn K g ∧ ConformalTo g z ∧
      ConformalTo (z - g) z ∧
      (supportFinset (z - g)).card < (supportFinset z).card := by
  classical
  obtain ⟨g0, hg0elem, hg0conf⟩ := exists_elementary_conformal K hzK hz0
  have hg00 : g0 ≠ 0 := hg0elem.1
  have hD : (supportFinset g0).Nonempty := by
    by_contra hnone
    have hzero : supportFinset g0 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
    apply hg00
    funext i
    by_contra hi
    have : i ∈ supportFinset g0 := by simpa using hi
    simpa [hzero] using this
  obtain ⟨q, hqD, hmin⟩ :=
    (supportFinset g0).exists_min_image (fun i => |z i| / |g0 i|) hD
  have hgq0 : g0 q ≠ 0 := by simpa using hqD
  have hzq0 : z q ≠ 0 := by
    have hsub := conformalTo_support_subset hg0conf
    have hqSupp : q ∈ Function.support g0 := by simpa [Function.mem_support] using hgq0
    have := hsub hqSupp
    simpa [Function.mem_support] using this
  let c : ℝ := |z q| / |g0 q|
  have hcpos : 0 < c := div_pos (abs_pos.mpr hzq0) (abs_pos.mpr hgq0)
  have hc0 : 0 ≤ c := le_of_lt hcpos
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have habs : ∀ i, |c * g0 i| ≤ |z i| := by
    intro i
    by_cases hgi0 : g0 i = 0
    · simp [hgi0]
    · have hiD : i ∈ supportFinset g0 := by simpa using hgi0
      have hle := hmin i hiD
      have hmul := mul_le_mul_of_nonneg_right hle (abs_nonneg (g0 i))
      have habsgi : |g0 i| ≠ 0 := abs_ne_zero.mpr hgi0
      calc
        |c * g0 i| = c * |g0 i| := by rw [abs_mul, abs_of_nonneg hc0]
        _ ≤ (|z i| / |g0 i|) * |g0 i| := by simpa [c] using hmul
        _ = |z i| := by field_simp [habsgi]
  let g : Fin n → ℝ := c • g0
  have hgconf : ConformalTo g z := by
    intro i
    constructor
    · simp only [g, Pi.smul_apply, smul_eq_mul]
      have hs := (hg0conf i).1
      nlinarith
    · simpa only [g, Pi.smul_apply, smul_eq_mul] using habs i
  have hgelem : IsElementaryIn K g := by
    exact isElementaryIn_smul K hg0elem hcne
  have hresconf : ConformalTo (z - g) z := conformalTo_sub_right hgconf
  have hcancel : g q = z q := by
    dsimp [g, c]
    simp only [Pi.smul_apply, smul_eq_mul]
    rcases lt_or_gt_of_ne hzq0 with hzneg | hzpos
    · have hgqle : g0 q ≤ 0 :=
        conformalTo_coord_nonpos_of_right_nonpos hg0conf (le_of_lt hzneg)
      have hgqneg : g0 q < 0 := lt_of_le_of_ne hgqle (Ne.symm hgq0)
      rw [abs_of_neg hzneg, abs_of_neg hgqneg]
      field_simp [hgq0]
      ring
    · have hgqge : 0 ≤ g0 q :=
        conformalTo_coord_nonneg_of_right_nonneg hg0conf (le_of_lt hzpos)
      have hgqpos : 0 < g0 q := lt_of_le_of_ne hgqge hgq0
      rw [abs_of_pos hzpos, abs_of_pos hgqpos]
      field_simp [hgq0]
  have hsub : supportFinset (z - g) ⊆ supportFinset z := by
    intro i hi
    simp only [mem_supportFinset] at hi ⊢
    intro hzi
    have hzres := conformalTo_eq_zero_of_right_eq_zero hresconf hzi
    exact hi hzres
  have hqIn : q ∈ supportFinset z := by simpa using hzq0
  have hqOut : q ∉ supportFinset (z - g) := by
    simp only [mem_supportFinset, not_not, Pi.sub_apply]
    rw [hcancel, sub_self]
  have hne : supportFinset (z - g) ≠ supportFinset z := by
    intro heq
    exact hqOut (heq.symm ▸ hqIn)
  have hstrict : supportFinset (z - g) ⊂ supportFinset z :=
    ssubset_of_ne_of_subset hne hsub
  exact ⟨g, hgelem, hgconf, hresconf, Finset.card_lt_card hstrict⟩

#print axioms half_perturb_conformal
#print axioms exists_elementary_conformal
#print axioms exists_saturating_elementary_conformal

end HirschCircuit
