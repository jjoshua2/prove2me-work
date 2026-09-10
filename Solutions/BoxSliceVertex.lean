import Mathlib
import Solutions.BoxSliceExchange
open Set Hirsch HirschBoxSlice
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HirschBoxSlice
variable {d : ℕ}

lemma extreme_at_most_one_interior
    (cap : Fin d → ℝ) (total : ℝ) (x : Fin d → ℝ)
    (hx : x ∈ extremePoints ℝ (slice cap total))
    (p q : Fin d) (hp0 : 0 < x p) (hp1 : x p < cap p)
    (hq0 : 0 < x q) (hq1 : x q < cap q) : p = q := by
  by_contra hpq
  let ε : ℝ := min (min (x p) (cap p - x p)) (min (x q) (cap q - x q))
  have hε : 0 < ε :=
    lt_min (lt_min hp0 (sub_pos.mpr hp1)) (lt_min hq0 (sub_pos.mpr hq1))
  have hεp0 : ε ≤ x p := (min_le_left _ _).trans (min_le_left _ _)
  have hεp1 : ε ≤ cap p - x p := (min_le_left _ _).trans (min_le_right _ _)
  have hεq0 : ε ≤ x q := (min_le_right _ _).trans (min_le_left _ _)
  have hεq1 : ε ≤ cap q - x q := (min_le_right _ _).trans (min_le_right _ _)
  let a := exchange x p q ε
  let b := exchange x q p ε
  have ha : a ∈ slice cap total := exchange_mem cap total x p q hpq hx.1 ε hε.le hεp1 hεq0
  have hb : b ∈ slice cap total := exchange_mem cap total x q p (Ne.symm hpq) hx.1 ε hε.le hεq1 hεp0
  have hop : x ∈ openSegment ℝ a b := by
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
    funext k
    change (1 / 2 : ℝ) * a k + (1 / 2 : ℝ) * b k = x k
    dsimp [a, b, exchange]
    split_ifs <;> ring
  have hax : a = x := hx.2 ha hb hop
  have heq := congrFun hax p
  have hval : a p = x p + ε := exchange_at_p x p q hpq ε
  rw [hval] at heq
  linarith

lemma extreme_of_bound_except
    (cap : Fin d → ℝ) (total : ℝ) (x : Fin d → ℝ)
    (hx : x ∈ slice cap total) (j : Fin d)
    (hfixed : ∀ k, k ≠ j → x k = 0 ∨ x k = cap k) :
    x ∈ extremePoints ℝ (slice cap total) := by
  refine ⟨hx, ?_⟩
  intro y hy z hz hop
  obtain ⟨α, β, hα, hβ, hαβ, hcombo⟩ := hop
  have heq : ∀ k, k ≠ j → y k = x k := by
    intro k hkj
    have hc := congrFun hcombo k
    change α * y k + β * z k = x k at hc
    rcases hfixed k hkj with hx0 | hxc
    · rw [hx0] at hc ⊢
      by_contra hne
      have hpos : 0 < y k := lt_of_le_of_ne (hy.1 k).1 (Ne.symm hne)
      have hp := mul_pos hα hpos
      linarith [mul_nonneg hβ.le (hz.1 k).1]
    · rw [hxc] at hc ⊢
      by_contra hne
      have hlt : y k < cap k := lt_of_le_of_ne (hy.1 k).2 hne
      have hp := mul_pos hα (sub_pos.mpr hlt)
      have hw : α * cap k + β * cap k = cap k := by rw [← add_mul, hαβ, one_mul]
      nlinarith [mul_nonneg hβ.le (sub_nonneg.mpr (hz.1 k).2)]
  have hrest : (∑ k ∈ Finset.univ.erase j, y k) = ∑ k ∈ Finset.univ.erase j, x k := by
    apply Finset.sum_congr rfl
    intro k hk
    exact heq k (Finset.ne_of_mem_erase hk)
  have hsx := Finset.sum_erase_add Finset.univ x (Finset.mem_univ j)
  have hsy := Finset.sum_erase_add Finset.univ y (Finset.mem_univ j)
  have hj : y j = x j := by linarith [hx.2, hy.2]
  funext k
  by_cases hkj : k = j
  · simpa only [hkj] using hj
  · exact heq k hkj
end HirschBoxSlice
#print axioms HirschBoxSlice.extreme_at_most_one_interior
#print axioms HirschBoxSlice.extreme_of_bound_except
