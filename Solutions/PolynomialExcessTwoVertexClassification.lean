import Solutions.PolynomialExcessTwoConvexity

/-!
# All vertices of the normalized two-moment slice

Candidate continuation of main after PR85. This file has NOT been compiled.
No Lean-kernel or Prove2Me verification is claimed. See the accompanying
research note and exact-rational tests for the ordinary proof and evidence.

The support-domination argument avoids assuming generic moments, dimension,
nonemptiness, strict feasibility, or a pre-existing enumeration of vertices.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace HirschExcessTwo

/-- Unit mass at one coordinate. This is feasible exactly when its moment
is the prescribed moment. -/
def singletonPoint {n : ℕ} (i : Fin n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun k => if k = i then 1 else 0)

@[simp] lemma singletonPoint_apply {n : ℕ} (i k : Fin n) :
    singletonPoint i k = if k = i then 1 else 0 := rfl

lemma singletonPoint_mem {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i : Fin n) (hi : t i = mu) :
    singletonPoint i ∈ momentSlice t mu := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro k
    simp only [singletonPoint_apply]
    split_ifs <;> norm_num
  · change (∑ k : Fin n, if k = i then (1 : ℝ) else 0) = 1
    simp
  · change (∑ k : Fin n, t k * (if k = i then (1 : ℝ) else 0)) = mu
    simp [mul_ite, hi]

lemma eq_singletonPoint_of_zero_off {n : ℕ}
    (s : EuclideanSpace ℝ (Fin n)) (i : Fin n)
    (hmass : (∑ k, s k) = 1)
    (hzero : ∀ k, k ≠ i → s k = 0) : s = singletonPoint i := by
  classical
  have hsum : (∑ k, s k) = s i := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      exact hzero k hki
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  have hsi : s i = 1 := hsum.symm.trans hmass
  ext k
  change s k = singletonPoint i k
  by_cases hki : k = i
  · subst k
    simpa using hsi
  · simp [singletonPoint_apply, hki, hzero k hki]

/-- Equal-moment singletons are extreme, including repeated equal moments. -/
theorem singletonPoint_mem_extremePoints {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i : Fin n) (hi : t i = mu) :
    singletonPoint i ∈ extremePoints ℝ (momentSlice t mu) := by
  classical
  have hp := singletonPoint_mem t mu i hi
  rw [mem_extremePoints_iff_left]
  refine ⟨hp, ?_⟩
  intro x hx y hy hseg
  apply eq_singletonPoint_of_zero_off x i hx.2.1
  intro k hki
  have hpzero : singletonPoint i ∈ zeroFace t mu k := by
    refine ⟨hp, ?_⟩
    simp [singletonPoint_apply, hki]
  exact ((zeroFace_isExtreme t mu k).left_mem_of_mem_openSegment
    hx hy hpzero hseg).2

/-- A finite positive margin absorbs a sufficiently small common perturbation.
The proof is elementary finite induction; no optimization oracle is used. -/
private theorem exists_positive_small_scale
    {ι : Type*} (S : Finset ι) (c r : ι → ℝ) :
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

/-- An extreme point equals every feasible point supported inside its positive
coordinates. This supplies classification without a support-rank assumption. -/
theorem extreme_eq_of_support_contained {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ)
    (x y : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ extremePoints ℝ (momentSlice t mu))
    (hy : y ∈ momentSlice t mu)
    (hsupp : ∀ k, x k = 0 → y k = 0) : x = y := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun k => 0 < x k)
  obtain ⟨ε, hε, hsmall⟩ := exists_positive_small_scale S
    (fun k => y k) (fun k => x k)
    (by intro k hk; exact (Finset.mem_filter.mp hk).2)
  let θ : ℝ := min ε (1 / 2)
  have hθ : 0 < θ := lt_min hε (by norm_num)
  have hθε : θ ≤ ε := min_le_left _ _
  have hθhalf : θ ≤ 1 / 2 := min_le_right _ _
  have hθ1 : θ < 1 := by linarith
  have hden : 0 < 1 - θ := sub_pos.mpr hθ1
  have hdom : ∀ k, θ * y k ≤ x k := by
    intro k
    by_cases hk : 0 < x k
    · have hkS : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
      have hbound := hsmall k hkS
      rw [abs_of_nonneg (hy.1 k)] at hbound
      exact (mul_le_mul_of_nonneg_right hθε (hy.1 k)).trans hbound.le
    · have hx0 : x k = 0 := le_antisymm (le_of_not_gt hk) (hx.1.1 k)
      rw [hx0, hsupp k hx0, mul_zero]
  let z : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 (fun k => (x k - θ * y k) / (1 - θ))
  have hzcoord (k : Fin n) : z k = (x k - θ * y k) / (1 - θ) := rfl
  have hz : z ∈ momentSlice t mu := by
    refine ⟨?_, ?_, ?_⟩
    · intro k
      rw [hzcoord]
      exact div_nonneg (sub_nonneg.mpr (hdom k)) hden.le
    · change (∑ k, (x k - θ * y k) / (1 - θ)) = 1
      rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
        hx.1.2.1, hy.2.1, mul_one]
      exact div_self (ne_of_gt hden)
    · change (∑ k, t k * ((x k - θ * y k) / (1 - θ))) = mu
      calc
        (∑ k, t k * ((x k - θ * y k) / (1 - θ))) =
            (∑ k, (t k * x k - θ * (t k * y k))) / (1 - θ) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = (mu - θ * mu) / (1 - θ) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hx.1.2.2, hy.2.2]
        _ = mu := by field_simp [ne_of_gt hden]; ring
  have hcomb : θ • y + (1 - θ) • z = x := by
    ext k
    change θ * y k + (1 - θ) * z k = x k
    rw [hzcoord]
    field_simp [ne_of_gt hden]
    ring
  have hseg : x ∈ openSegment ℝ y z := by
    apply mem_openSegment_iff_div.mpr
    refine ⟨θ, 1 - θ, hθ, hden, ?_⟩
    have hsum : θ + (1 - θ) = 1 := by ring
    simpa only [hsum, div_one] using hcomb
  exact (hx.2 hy hz hseg).symm

/-- A feasible distribution either has a positive equal-moment coordinate,
or has positive coordinates strictly on both sides of the target moment. -/
theorem feasible_support_has_singleton_or_pair {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ momentSlice t mu) :
    (∃ k : Fin n, 0 < x k ∧ t k = mu) ∨
      ∃ i j : Fin n, 0 < x i ∧ 0 < x j ∧ t i < mu ∧ mu < t j := by
  classical
  by_cases he : ∃ k : Fin n, 0 < x k ∧ t k = mu
  · exact Or.inl he
  right
  have hne (k : Fin n) (hk : 0 < x k) : t k ≠ mu := by
    intro h
    exact he ⟨k, hk, h⟩
  have hpos : ∃ k : Fin n, 0 < x k := by
    by_contra h
    have hz : ∀ k, x k = 0 := by
      intro k
      exact le_antisymm (le_of_not_gt (fun hk => h ⟨k, hk⟩)) (hx.1 k)
    have hsum : (∑ k, x k) = 0 := by simp [hz]
    linarith [hx.2.1]
  obtain ⟨r, hr⟩ := hpos
  have hsum : (∑ k, (t k - mu) * x k) = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hx.2.2, hx.2.1]
    ring
  have hsum' : (∑ k, (mu - t k) * x k) = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hx.2.2, hx.2.1]
    ring
  have hl : ∃ i : Fin n, 0 < x i ∧ t i < mu := by
    by_contra h
    have hge (k : Fin n) (hk : 0 < x k) : mu ≤ t k :=
      le_of_not_gt (fun ht => h ⟨k, hk, ht⟩)
    have hnn : ∀ k : Fin n, 0 ≤ (t k - mu) * x k := by
      intro k
      by_cases hk : 0 < x k
      · exact mul_nonneg (sub_nonneg.mpr (hge k hk)) (hx.1 k)
      · have hz : x k = 0 := le_antisymm (le_of_not_gt hk) (hx.1 k)
        simp [hz]
    have htr : mu < t r := lt_of_le_of_ne (hge r hr) (hne r hr).symm
    have hp : 0 < (t r - mu) * x r := mul_pos (sub_pos.mpr htr) hr
    have hb := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => hnn k)
      (Finset.mem_univ r)
    rw [hsum] at hb
    linarith
  have hh : ∃ j : Fin n, 0 < x j ∧ mu < t j := by
    by_contra h
    have hle (k : Fin n) (hk : 0 < x k) : t k ≤ mu :=
      le_of_not_gt (fun ht => h ⟨k, hk, ht⟩)
    have hnn : ∀ k : Fin n, 0 ≤ (mu - t k) * x k := by
      intro k
      by_cases hk : 0 < x k
      · exact mul_nonneg (sub_nonneg.mpr (hle k hk)) (hx.1 k)
      · have hz : x k = 0 := le_antisymm (le_of_not_gt hk) (hx.1 k)
        simp [hz]
    have htr : t r < mu := lt_of_le_of_ne (hle r hr) (hne r hr)
    have hp : 0 < (mu - t r) * x r := mul_pos (sub_pos.mpr htr) hr
    have hb := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => hnn k)
      (Finset.mem_univ r)
    rw [hsum'] at hb
    linarith
  obtain ⟨i, hi, hti⟩ := hl
  obtain ⟨j, hj, htj⟩ := hh
  exact ⟨i, j, hi, hj, hti, htj⟩

/-- Complete classification, not just existence of the listed vertices. -/
theorem momentSlice_extremePoints_iff {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ extremePoints ℝ (momentSlice t mu) ↔
      (∃ k : Fin n, t k = mu ∧ x = singletonPoint k) ∨
      (∃ i j : Fin n, t i < mu ∧ mu < t j ∧ x = pairPoint t mu i j) := by
  classical
  constructor
  · intro hx
    rcases feasible_support_has_singleton_or_pair t mu x hx.1 with
      ⟨k, hk, htk⟩ | ⟨i, j, hi, hj, hti, htj⟩
    · left
      refine ⟨k, htk, ?_⟩
      apply extreme_eq_of_support_contained t mu x (singletonPoint k) hx
        (singletonPoint_mem t mu k htk)
      intro r hr
      have hrk : r ≠ k := by intro h; subst r; linarith
      simp [singletonPoint_apply, hrk]
    · right
      refine ⟨i, j, hti, htj, ?_⟩
      apply extreme_eq_of_support_contained t mu x (pairPoint t mu i j) hx
        (pairPoint_mem t mu i j hti htj)
      intro r hr
      have hri : r ≠ i := by intro h; subst r; linarith
      have hrj : r ≠ j := by intro h; subst r; linarith
      exact pairPoint_apply_other t mu i j r hri hrj
  · rintro (⟨k, hk, rfl⟩ | ⟨i, j, hi, hj, rfl⟩)
    · exact singletonPoint_mem_extremePoints t mu k hk
    · exact pairPoint_mem_extremePoints t mu i j hi hj

#print axioms singletonPoint_mem_extremePoints
#print axioms extreme_eq_of_support_contained
#print axioms feasible_support_has_singleton_or_pair
#print axioms momentSlice_extremePoints_iff

end HirschExcessTwo
