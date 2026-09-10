import Mathlib
import Solutions.BoxSlicePivotBasics
open Set Hirsch
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HirschBoxSlice
variable {d : ℕ}

lemma interior_ne_bound_target {cap x v : Fin d → ℝ} {k : Fin d}
    (hx : Inside cap x k) (hv : AtBound cap v k) : x k ≠ v k := by
  intro heq
  rcases hv with h | h <;> rcases hx with ⟨h0, h1⟩ <;> linarith

/-- With both mismatch signs present and the buffer at a bound, choose
opposite mismatches containing the possible interior coordinate. -/
lemma select_both (cap : Fin d → ℝ) (total : ℝ) (x v : Fin d → ℝ) (j : Fin d)
    (hx : x ∈ slice cap total) (hr : Regular cap x)
    (hv : ∀ k, k ≠ j → AtBound cap v k)
    (hj : AtBound cap x j) (hi : Inc v j x) (hd : Dec v j x) :
    ∃ p q : Fin d, p ≠ q ∧ p ≠ j ∧ q ≠ j ∧ x p < v p ∧ v q < x q ∧
      ∀ k, k ≠ p → k ≠ q → AtBound cap x k := by
  classical
  by_cases hf : ∃ k, Inside cap x k
  · obtain ⟨k, hk⟩ := hf
    have hkj : k ≠ j := by
      intro heq
      subst k
      exact not_inside_of_bound hj hk
    have hkv := interior_ne_bound_target hk (hv k hkj)
    rcases lt_or_gt_of_ne hkv with hki | hkd
    · obtain ⟨q, hqj, hq⟩ := hd
      have hkq : k ≠ q := by intro heq; subst q; linarith
      refine ⟨k, q, hkq, hkj, hqj, hki, hq, ?_⟩
      intro l hlk hlq
      exact bounds_except_inside cap total x hx hr k hk l hlk
    · obtain ⟨p, hpj, hp⟩ := hi
      have hpk : p ≠ k := by intro heq; subst p; linarith
      refine ⟨p, k, hpk, hpj, hkj, hp, hkd, ?_⟩
      intro l hlp hlk
      exact bounds_except_inside cap total x hx hr k hk l hlk
  · obtain ⟨p, hpj, hp⟩ := hi
    obtain ⟨q, hqj, hq⟩ := hd
    have hpq : p ≠ q := by intro heq; subst q; linarith
    refine ⟨p, q, hpq, hpj, hqj, hp, hq, ?_⟩
    intro k hkp hkq
    exact bound_of_not_inside cap total x hx k (fun hk => hf ⟨k, hk⟩)

lemma select_inc_buffer (cap : Fin d → ℝ) (total : ℝ) (x v : Fin d → ℝ) (j : Fin d)
    (hx : x ∈ slice cap total) (hr : Regular cap x)
    (hv : ∀ k, k ≠ j → AtBound cap v k)
    (hi : Inc v j x) (hd : ¬ Dec v j x) :
    ∃ p, p ≠ j ∧ x p < v p ∧ ∀ k, k ≠ p → k ≠ j → AtBound cap x k := by
  classical
  by_cases hf : ∃ k, k ≠ j ∧ Inside cap x k
  · obtain ⟨k, hkj, hk⟩ := hf
    have hkv := interior_ne_bound_target hk (hv k hkj)
    have hle : x k ≤ v k := le_of_not_gt (fun h => hd ⟨k, hkj, h⟩)
    refine ⟨k, hkj, lt_of_le_of_ne hle hkv, ?_⟩
    intro l hlk hlj
    exact bounds_except_inside cap total x hx hr k hk l hlk
  · obtain ⟨p, hpj, hp⟩ := hi
    refine ⟨p, hpj, hp, ?_⟩
    intro k hkp hkj
    exact bound_of_not_inside cap total x hx k (fun hk => hf ⟨k, hkj, hk⟩)

lemma select_dec_buffer (cap : Fin d → ℝ) (total : ℝ) (x v : Fin d → ℝ) (j : Fin d)
    (hx : x ∈ slice cap total) (hr : Regular cap x)
    (hv : ∀ k, k ≠ j → AtBound cap v k)
    (hi : ¬ Inc v j x) (hd : Dec v j x) :
    ∃ q, q ≠ j ∧ v q < x q ∧ ∀ k, k ≠ j → k ≠ q → AtBound cap x k := by
  classical
  by_cases hf : ∃ k, k ≠ j ∧ Inside cap x k
  · obtain ⟨k, hkj, hk⟩ := hf
    have hkv := interior_ne_bound_target hk (hv k hkj)
    have hle : v k ≤ x k := le_of_not_gt (fun h => hi ⟨k, hkj, h⟩)
    refine ⟨k, hkj, lt_of_le_of_ne hle hkv.symm, ?_⟩
    intro l hlj hlk
    exact bounds_except_inside cap total x hx hr k hk l hlk
  · obtain ⟨q, hqj, hq⟩ := hd
    refine ⟨q, hqj, hq, ?_⟩
    intro k hkj hkq
    exact bound_of_not_inside cap total x hx k (fun hk => hf ⟨k, hkj, hk⟩)

/-- If every nonbuffer mismatch needs an increase, the buffer has enough
mass to fill any one of them completely. A tie is harmless. -/
lemma inc_buffer_capacity (cap : Fin d → ℝ) (total : ℝ) (x v : Fin d → ℝ) (j p : Fin d)
    (hx : x ∈ slice cap total) (hv : v ∈ slice cap total)
    (hpj : p ≠ j) (hvp : v p = cap p) (hd : ¬ Dec v j x) :
    cap p - x p ≤ x j := by
  have hle : ∀ k, k ≠ j → x k ≤ v k :=
    fun k hk => le_of_not_gt (fun h => hd ⟨k, hk, h⟩)
  have hsx := Finset.sum_erase_add Finset.univ x (Finset.mem_univ j)
  have hsv := Finset.sum_erase_add Finset.univ v (Finset.mem_univ j)
  have hbalance : (∑ k ∈ Finset.univ.erase j, (v k - x k)) = x j - v j := by
    rw [Finset.sum_sub_distrib]
    linarith [hx.2, hv.2]
  have hcoord : v p - x p ≤ ∑ k ∈ Finset.univ.erase j, (v k - x k) :=
    Finset.single_le_sum (fun k hk => sub_nonneg.mpr (hle k (Finset.ne_of_mem_erase hk)))
      (by simp [hpj])
  have hvj := (hv.1 j).1
  rw [hvp] at hcoord
  linarith

lemma dec_buffer_capacity (cap : Fin d → ℝ) (total : ℝ) (x v : Fin d → ℝ) (j q : Fin d)
    (hx : x ∈ slice cap total) (hv : v ∈ slice cap total)
    (hqj : q ≠ j) (hvq : v q = 0) (hi : ¬ Inc v j x) :
    x q ≤ cap j - x j := by
  have hle : ∀ k, k ≠ j → v k ≤ x k :=
    fun k hk => le_of_not_gt (fun h => hi ⟨k, hk, h⟩)
  have hsx := Finset.sum_erase_add Finset.univ x (Finset.mem_univ j)
  have hsv := Finset.sum_erase_add Finset.univ v (Finset.mem_univ j)
  have hbalance : (∑ k ∈ Finset.univ.erase j, (x k - v k)) = v j - x j := by
    rw [Finset.sum_sub_distrib]
    linarith [hx.2, hv.2]
  have hcoord : x q - v q ≤ ∑ k ∈ Finset.univ.erase j, (x k - v k) :=
    Finset.single_le_sum (fun k hk => sub_nonneg.mpr (hle k (Finset.ne_of_mem_erase hk)))
      (by simp [hqj])
  have hvj := (hv.1 j).2
  rw [hvq] at hcoord
  linarith

lemma exchange_preserves (x v : Fin d → ℝ) (j p q : Fin d) (ε : ℝ)
    (hp : p ≠ j → x p ≠ v p) (hq : q ≠ j → x q ≠ v q) :
    Preserves v j x (exchange x p q ε) := by
  intro k hkj heq
  by_cases hkp : k = p
  · subst k
    exact False.elim (hp hkj heq)
  · by_cases hkq : k = q
    · subst k
      exact False.elim (hq hkj heq)
    · rw [exchange_elsewhere x p q k hkp hkq ε]
      exact heq
end HirschBoxSlice
