import Mathlib
import Solutions.PolynomialExcessTwoSupportFaces

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 3000000
set_option autoImplicit false

noncomputable section

namespace HirschExcessTwo

/-- The equal-moment singleton vertex. -/
def singletonPoint {n : ℕ} (i : Fin n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun k => if k = i then 1 else 0)

@[simp] lemma singletonPoint_apply {n : ℕ} (i k : Fin n) :
    singletonPoint i k = if k = i then 1 else 0 := rfl

lemma singletonPoint_mem {n : ℕ} (t : Fin n → ℝ) (mu : ℝ)
    (i : Fin n) (hi : t i = mu) : singletonPoint i ∈ momentSlice t mu := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro k
    simp only [singletonPoint_apply]
    split_ifs <;> norm_num
  · change (∑ k, if k = i then (1 : ℝ) else 0) = 1
    simp
  · change (∑ k, t k * (if k = i then (1 : ℝ) else 0)) = mu
    simpa [mul_ite] using hi

lemma eq_singletonPoint_of_mem_of_zero_off_singleton {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i : Fin n)
    (s : EuclideanSpace ℝ (Fin n)) (hs : s ∈ momentSlice t mu)
    (hzero : ∀ k, k ≠ i → s k = 0) : s = singletonPoint i := by
  classical
  have hsum : (∑ k, s k) = s i := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      exact hzero k hki
    · simp
  have hsi : s i = 1 := hsum.symm.trans hs.2.1
  ext k
  by_cases hki : k = i
  · subst k
    simpa using hsi
  · simp [singletonPoint_apply, hki, hzero k hki]

theorem singletonPoint_mem_extremePoints {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i : Fin n) (hi : t i = mu) :
    singletonPoint i ∈ extremePoints ℝ (momentSlice t mu) := by
  classical
  have hp := singletonPoint_mem t mu i hi
  rw [mem_extremePoints_iff_left]
  refine ⟨hp, ?_⟩
  intro x hx y hy hseg
  apply eq_singletonPoint_of_mem_of_zero_off_singleton t mu i x hx
  intro k hki
  have hpzero : singletonPoint i ∈ zeroFace t mu k := by
    exact ⟨hp, by simp [singletonPoint_apply, hki]⟩
  exact ((zeroFace_isExtreme t mu k).left_mem_of_mem_openSegment
    hx hy hpzero hseg).2

/-- Every feasible point supports an explicit singleton or low/high pair
vertex. This selector preserves every coordinate that is zero at the input. -/
theorem exists_supported_canonical_vertex {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (s : EuclideanSpace ℝ (Fin n))
    (hs : s ∈ momentSlice t mu) :
    (∃ i : Fin n, 0 < s i ∧ t i = mu) ∨
      ∃ i j : Fin n, 0 < s i ∧ 0 < s j ∧ t i < mu ∧ mu < t j := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun i => 0 < s i)
  have hS : S.Nonempty := by
    by_contra hn
    have hz : ∀ i, s i = 0 := by
      intro i
      have hnot : ¬ 0 < s i := by
        intro hp
        exact hn ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hp⟩⟩
      exact le_antisymm (le_of_not_gt hnot) (hs.1 i)
    have hbad := hs.2.1
    simp [hz] at hbad
  obtain ⟨i, hiS, hmin⟩ := S.exists_min_image t hS
  obtain ⟨j, hjS, hmax⟩ := S.exists_max_image t hS
  have hi : 0 < s i := (Finset.mem_filter.mp hiS).2
  have hj : 0 < s j := (Finset.mem_filter.mp hjS).2
  have hminrow : ∀ k, t i * s k ≤ t k * s k := by
    intro k
    by_cases hk : 0 < s k
    · exact mul_le_mul_of_nonneg_right
        (hmin k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩)) (hs.1 k)
    · have hzero : s k = 0 := le_antisymm (le_of_not_gt hk) (hs.1 k)
      simp [hzero]
  have hmaxrow : ∀ k, t k * s k ≤ t j * s k := by
    intro k
    by_cases hk : 0 < s k
    · exact mul_le_mul_of_nonneg_right
        (hmax k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩)) (hs.1 k)
    · have hzero : s k = 0 := le_antisymm (le_of_not_gt hk) (hs.1 k)
      simp [hzero]
  have hile : t i ≤ mu := by
    have h := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) => hminrow k)
    simpa only [← Finset.mul_sum, hs.2.1, hs.2.2, mul_one] using h
  have hjge : mu ≤ t j := by
    have h := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) => hmaxrow k)
    simpa only [← Finset.mul_sum, hs.2.1, hs.2.2, mul_one] using h
  by_cases heqi : t i = mu
  · exact Or.inl ⟨i, hi, heqi⟩
  by_cases heqj : t j = mu
  · exact Or.inl ⟨j, hj, heqj⟩
  exact Or.inr ⟨i, j, hi, hj, lt_of_le_of_ne hile heqi,
    lt_of_le_of_ne hjge (Ne.symm heqj)⟩

private lemma exists_pos_mul_abs_lt {ι : Type*}
    (S : Finset ι) (c r : ι → ℝ) :
    (∀ i ∈ S, 0 < r i) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ S, ε * |c i| < r i := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨1, by norm_num, ?_⟩
      simp
  | @insert i S hi ih =>
      intro hr
      obtain ⟨ε, hε, hS⟩ := ih (fun j hj => hr j (Finset.mem_insert_of_mem hj))
      have hri : 0 < r i := hr i (Finset.mem_insert_self i S)
      have hden : 0 < |c i| + 1 := by positivity
      let δ : ℝ := min ε (r i / (|c i| + 1))
      have hδ : 0 < δ := lt_min hε (div_pos hri hden)
      have hδε : δ ≤ ε := min_le_left _ _
      have hδr : δ * (|c i| + 1) ≤ r i :=
        (le_div_iff₀ hden).mp (min_le_right _ _)
      refine ⟨δ / 2, by positivity, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hjS
      · subst j
        nlinarith [abs_nonneg (c i)]
      · calc
          (δ / 2) * |c j| ≤ ε * |c j| :=
            mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg (c j))
          _ < r j := hS j hjS

/-- At an extreme point, any feasible point with no additional positive
coordinates must coincide with it. The proof extends a segment a small
positive distance past the extreme point. -/
theorem extreme_eq_of_zero_imp_zero {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (x p : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ extremePoints ℝ (momentSlice t mu))
    (hp : p ∈ momentSlice t mu)
    (hzero : ∀ i, x i = 0 → p i = 0) : x = p := by
  classical
  have hxP := (mem_extremePoints_iff_left.mp hx).1
  let S : Finset (Fin n) := Finset.univ.filter (fun i => 0 < x i)
  obtain ⟨ε, hε, hsmall⟩ := exists_pos_mul_abs_lt S
    (fun i => x i - p i) (fun i => x i)
    (fun i hi => (Finset.mem_filter.mp hi).2)
  let q : EuclideanSpace ℝ (Fin n) := x + ε • (x - p)
  have hq : q ∈ momentSlice t mu := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      change 0 ≤ x i + ε * (x i - p i)
      by_cases hi : 0 < x i
      · have hb := hsmall i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
        have hab : -(ε * |x i - p i|) ≤ ε * (x i - p i) := by
          have h := mul_le_mul_of_nonneg_left (neg_abs_le (x i - p i)) hε.le
          nlinarith
        linarith
      · have hxi : x i = 0 := le_antisymm (le_of_not_gt hi) (hxP.1 i)
        rw [hxi, hzero i hxi]
        ring_nf
        exact le_rfl
    · change (∑ i, (x i + ε * (x i - p i))) = 1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
        hxP.2.1, hp.2.1]
      ring
    · change (∑ i, t i * (x i + ε * (x i - p i))) = mu
      calc
        (∑ i, t i * (x i + ε * (x i - p i))) =
            ∑ i, (t i * x i + ε * (t i * x i - t i * p i)) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = mu := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum,
            Finset.sum_sub_distrib, hxP.2.2, hp.2.2]
          ring
  have hseg : x ∈ openSegment ℝ p q := by
    refine mem_openSegment_iff_div.mpr ⟨ε, 1, hε, by norm_num, ?_⟩
    ext i
    change (ε / (ε + 1)) * p i + (1 / (ε + 1)) *
      (x i + ε * (x i - p i)) = x i
    have hden : ε + 1 ≠ 0 := ne_of_gt (by linarith)
    field_simp
    ring
  exact ((mem_extremePoints_iff_left.mp hx).2 p hp q hq hseg).symm

/-- Complete extreme-point classification, including repeated moment values
and equal-moment singleton vertices. No generic-position assumption is used. -/
theorem extremePoints_classification {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ extremePoints ℝ (momentSlice t mu)) :
    (∃ i : Fin n, t i = mu ∧ x = singletonPoint i) ∨
      ∃ i j : Fin n, t i < mu ∧ mu < t j ∧ x = pairPoint t mu i j := by
  classical
  have hxP := (mem_extremePoints_iff_left.mp hx).1
  rcases exists_supported_canonical_vertex t mu x hxP with ⟨i, hi, hti⟩ |
    ⟨i, j, hi, hj, hli, hrj⟩
  · left
    refine ⟨i, hti, extreme_eq_of_zero_imp_zero t mu x (singletonPoint i)
      hx (singletonPoint_mem t mu i hti) ?_⟩
    intro k hk
    have hki : k ≠ i := by intro h; subst k; linarith
    simp [singletonPoint_apply, hki]
  · right
    refine ⟨i, j, hli, hrj, extreme_eq_of_zero_imp_zero t mu x (pairPoint t mu i j)
      hx (pairPoint_mem t mu i j hli hrj) ?_⟩
    intro k hk
    have hki : k ≠ i := by intro h; subst k; linarith
    have hkj : k ≠ j := by intro h; subst k; linarith
    exact pairPoint_apply_other t mu i j k hki hkj

/-- A face-preserving vertex selector for arbitrary feasible checkpoints. -/
theorem exists_extremePoint_preserving_zeros {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (s : EuclideanSpace ℝ (Fin n))
    (hs : s ∈ momentSlice t mu) :
    ∃ p ∈ extremePoints ℝ (momentSlice t mu), ∀ i, s i = 0 → p i = 0 := by
  classical
  rcases exists_supported_canonical_vertex t mu s hs with ⟨i, hi, hti⟩ |
    ⟨i, j, hi, hj, hli, hrj⟩
  · refine ⟨singletonPoint i, singletonPoint_mem_extremePoints t mu i hti, ?_⟩
    intro k hk
    have hki : k ≠ i := by intro h; subst k; linarith
    simp [singletonPoint_apply, hki]
  · refine ⟨pairPoint t mu i j, pairPoint_mem_extremePoints t mu i j hli hrj, ?_⟩
    intro k hk
    have hki : k ≠ i := by intro h; subst k; linarith
    have hkj : k ≠ j := by intro h; subst k; linarith
    exact pairPoint_apply_other t mu i j k hki hkj

#print axioms singletonPoint_mem_extremePoints
#print axioms exists_supported_canonical_vertex
#print axioms extreme_eq_of_zero_imp_zero
#print axioms extremePoints_classification
#print axioms exists_extremePoint_preserving_zeros

end HirschExcessTwo
