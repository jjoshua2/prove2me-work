import Mathlib
import Solutions.CircuitConformal

open Set HirschSlack HirschCircuitProgress HirschAugment HirschConformal

set_option maxHeartbeats 6000000

noncomputable section

namespace HirschCircuitNorm

lemma large_list_summand {E : Type*} (parts : List E) (f : E → ℝ)
    (M : ℝ) (hlen : (parts.length : ℝ) ≤ M)
    (hpos : 0 < (parts.map f).sum) :
    ∃ g ∈ parts, 0 < f g ∧ (parts.map f).sum ≤ M * f g := by
  classical
  have hpne : parts ≠ [] := by
    intro h
    simp only [h, List.map_nil, List.sum_nil, lt_self_iff_false] at hpos
  have hsne : parts.toFinset.Nonempty := by
    obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil parts hpne
    exact ⟨g, List.mem_toFinset.mpr hg⟩
  obtain ⟨g, hg, hmax⟩ := parts.toFinset.exists_min_image (fun x => -f x) hsne
  have hbound : ∀ x ∈ parts, f x ≤ f g := by
    intro x hx
    have h := hmax x (List.mem_toFinset.mpr hx)
    linarith
  have sum_bound : ∀ l : List E, (∀ x ∈ l, f x ≤ f g) →
      (l.map f).sum ≤ (l.length : ℝ) * f g := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro hb
      have ha := hb a (List.mem_cons_self ..)
      have hl := ih (fun x hx => hb x (List.mem_cons_of_mem a hx))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
        Nat.cast_one]
      nlinarith
  have hsum := sum_bound parts hbound
  have hfg : 0 < f g := by
    by_contra hn
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos
      (Nat.cast_nonneg parts.length) (le_of_not_gt hn)
    linarith
  exact ⟨g, List.mem_toFinset.mp hg, hfg,
    hsum.trans (mul_le_mul_of_nonneg_right hlen hfg.le)⟩

/-- The negative weighted mass is a linear functional on slack directions. -/
def gainMap {n : ℕ} (N : Finset (Fin n)) (weight : Fin n → ℝ) :
    (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun g := ∑ i ∈ N, weight i * (-g i)
  map_add' g h := by
    change (∑ i ∈ N, weight i * (-(g i + h i))) =
      (∑ i ∈ N, weight i * (-g i)) + (∑ i ∈ N, weight i * (-h i))
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  map_smul' c g := by
    change (∑ i ∈ N, weight i * (-(c * g i))) =
      c * (∑ i ∈ N, weight i * (-g i))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

/-- A complete norm-reduction augmentation: both the elementary direction and
its maximal positive feasible scalar are obtained, not assumed. This is a
circuit step and does not assert either endpoint is a vertex. -/
theorem exists_norm_reducing_circuit_step
    (n : ℕ) (K : Submodule ℝ (Fin n → ℝ)) (b x v : Fin n → ℝ)
    (N : Finset (Fin n)) (weight : Fin n → ℝ) (M : ℝ)
    (hM : 1 ≤ M) (hn : (n : ℝ) ≤ M)
    (hx : x ∈ standardSet K b) (hv : v ∈ standardSet K b)
    (hw : ∀ i ∈ N, 0 ≤ weight i) (hvN : ∀ i ∈ N, v i = 0)
    (hmass : 0 < ∑ i ∈ N, weight i * x i) :
    ∃ y : Fin n → ℝ,
      StandardStep K b x y ∧
      M * (∑ i ∈ N, weight i * y i) ≤
        (M - 1) * (∑ i ∈ N, weight i * x i) ∧
      (∀ i, x i ≤ M * v i → y i ≤ M * v i) ∧
      (∀ i ∈ N, y i ≤ x i) := by
  have hdelta : v - x ∈ K := by
    have h := K.sub_mem hv.1 hx.1
    convert h using 1 <;> module
  obtain ⟨parts, hsum, hlen, hparts⟩ := exists_conformal_decomposition K (v - x) hdelta
  let gain := gainMap N weight
  have hS : (parts.map gain).sum = ∑ i ∈ N, weight i * x i := by
    rw [← map_list_sum gain, hsum]
    change (∑ i ∈ N, weight i * (-(v i - x i))) = ∑ i ∈ N, weight i * x i
    apply Finset.sum_congr rfl
    intro i hi
    rw [hvN i hi, zero_sub, neg_neg]
  have hlenM : (parts.length : ℝ) ≤ M :=
    (Nat.cast_le.mpr hlen).trans hn
  obtain ⟨g, hgparts, hgainpos, hgain⟩ := large_list_summand parts gain M hlenM
    (by rw [hS]; exact hmass)
  have hgE := (hparts g hgparts).1
  have hgconf := (hparts g hgparts).2
  have hneg : ∃ i, g i < 0 := by
    by_contra h
    have hg0 : ∀ i, 0 ≤ g i := fun i => le_of_not_gt (fun hi => h ⟨i, hi⟩)
    have hnonpos : gain g ≤ 0 := Finset.sum_nonpos fun i hi =>
      mul_nonpos_of_nonneg_of_nonpos (hw i hi) (neg_nonpos.mpr (hg0 i))
    linarith
  have htangent : ∀ i, x i = 0 → 0 ≤ g i := by
    intro i hxi
    have hb := (conformal_bounds hgconf i).1
      (by change 0 ≤ v i - x i; rw [hxi, sub_zero]; exact hv.2 i)
    exact hb.1
  obtain ⟨alpha, ha, hstep, hhit, hunit⟩ :=
    elementary_maximal_step K b x g hx hgE htangent hneg
  have halpha1 : 1 ≤ alpha := hunit (conformal_unit_feasible x v g hx.2 hv.2 hgconf)
  have hselected : (∑ i ∈ N, weight i * x i) ≤
      M * (∑ i ∈ N, weight i * (-g i)) := by
    rw [hS] at hgain
    exact hgain
  have hnumerics := greedy_norm_step N x v g weight M alpha hM halpha1 hx.2 hv.2
    hw hvN hgconf hstep.2.1.2 hmass hselected
  exact ⟨x + alpha • g, hstep, hnumerics.2.1, hnumerics.2.2.1, hnumerics.2.2.2⟩

#print axioms exists_norm_reducing_circuit_step

end HirschCircuitNorm
