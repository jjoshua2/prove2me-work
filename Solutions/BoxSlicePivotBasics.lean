import Mathlib
import Solutions.BoxSliceVertex
open Set Hirsch
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HirschBoxSlice
variable {d : ℕ}

def AtBound (cap x : Fin d → ℝ) (k : Fin d) : Prop := x k = 0 ∨ x k = cap k
def Inside (cap x : Fin d → ℝ) (k : Fin d) : Prop := 0 < x k ∧ x k < cap k
def Regular (cap x : Fin d → ℝ) : Prop :=
  ∀ p q, Inside cap x p → Inside cap x q → p = q

def Inc (v : Fin d → ℝ) (j : Fin d) (x : Fin d → ℝ) : Prop :=
  ∃ k, k ≠ j ∧ x k < v k
def Dec (v : Fin d → ℝ) (j : Fin d) (x : Fin d → ℝ) : Prop :=
  ∃ k, k ≠ j ∧ v k < x k
def Mixed (cap v : Fin d → ℝ) (j : Fin d) (x : Fin d → ℝ) : Prop :=
  Inside cap x j ∧ Inc v j x ∧ Dec v j x
noncomputable def mismatches (v : Fin d → ℝ) (j : Fin d) (x : Fin d → ℝ) : Finset (Fin d) := by
  classical
  exact Finset.univ.filter (fun k => k ≠ j ∧ x k ≠ v k)
noncomputable def potential (cap v : Fin d → ℝ) (j : Fin d) (x : Fin d → ℝ) : ℕ := by
  classical
  exact (mismatches v j x).card + if Mixed cap v j x then 1 else 0

def Preserves (v : Fin d → ℝ) (j : Fin d) (x y : Fin d → ℝ) : Prop :=
  ∀ k, k ≠ j → x k = v k → y k = v k

lemma regular_of_extreme (cap : Fin d → ℝ) (total : ℝ) (x : Fin d → ℝ)
    (hx : x ∈ extremePoints ℝ (slice cap total)) : Regular cap x := by
  intro p q hp hq
  exact extreme_at_most_one_interior cap total x hx p q hp.1 hp.2 hq.1 hq.2

lemma bound_of_not_inside (cap : Fin d → ℝ) (total : ℝ) (x : Fin d → ℝ)
    (hx : x ∈ slice cap total) (k : Fin d) (hk : ¬ Inside cap x k) : AtBound cap x k := by
  by_cases hz : x k = 0
  · exact Or.inl hz
  · right
    by_contra hh
    exact hk ⟨lt_of_le_of_ne (hx.1 k).1 (Ne.symm hz), lt_of_le_of_ne (hx.1 k).2 hh⟩

lemma not_inside_of_bound {cap x : Fin d → ℝ} {k : Fin d}
    (h : AtBound cap x k) : ¬ Inside cap x k := by
  rintro ⟨h0, h1⟩
  rcases h with h | h <;> linarith

lemma bounds_except_inside (cap : Fin d → ℝ) (total : ℝ) (x : Fin d → ℝ)
    (hx : x ∈ slice cap total) (hr : Regular cap x)
    (k : Fin d) (hk : Inside cap x k) : ∀ l, l ≠ k → AtBound cap x l := by
  intro l hl
  exact bound_of_not_inside cap total x hx l (fun hi => hl (hr l k hi hk))

lemma target_upper_of_inc (cap : Fin d → ℝ) (total : ℝ) (x v : Fin d → ℝ)
    (hx : x ∈ slice cap total) {p : Fin d}
    (hb : AtBound cap v p) (hp : x p < v p) : v p = cap p := by
  rcases hb with hb | hb
  · have h0 := (hx.1 p).1
    linarith
  · exact hb
lemma target_lower_of_dec (cap : Fin d → ℝ) (total : ℝ) (x v : Fin d → ℝ)
    (hx : x ∈ slice cap total) {q : Fin d}
    (hb : AtBound cap v q) (hq : v q < x q) : v q = 0 := by
  rcases hb with hb | hb
  · exact hb
  · have h1 := (hx.1 q).2
    linarith

lemma eq_of_no_signs (total : ℝ) (cap x v : Fin d → ℝ) (j : Fin d)
    (hx : x ∈ slice cap total) (hv : v ∈ slice cap total)
    (hi : ¬ Inc v j x) (hd : ¬ Dec v j x) : x = v := by
  have heq : ∀ k, k ≠ j → x k = v k := by
    intro k hk
    apply le_antisymm
    · exact le_of_not_gt (fun h => hd ⟨k, hk, h⟩)
    · exact le_of_not_gt (fun h => hi ⟨k, hk, h⟩)
  have hr : (∑ k ∈ Finset.univ.erase j, x k) = ∑ k ∈ Finset.univ.erase j, v k :=
    Finset.sum_congr rfl (fun k hk => heq k (Finset.ne_of_mem_erase hk))
  have hsx := Finset.sum_erase_add Finset.univ x (Finset.mem_univ j)
  have hsv := Finset.sum_erase_add Finset.univ v (Finset.mem_univ j)
  have hj : x j = v j := by linarith [hx.2, hv.2]
  funext k
  by_cases hk : k = j
  · simpa only [hk] using hj
  · exact heq k hk

lemma potential_le_dim (cap v x : Fin d → ℝ) (j : Fin d) : potential cap v j x ≤ d := by
  classical
  have hs : mismatches v j x ⊆ Finset.univ.erase j := by
    intro k hk
    have h := (Finset.mem_filter.mp hk).2.1
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact h
  have hc := Finset.card_le_card hs
  have hj : 0 < d := j.pos
  have hc' : (mismatches v j x).card ≤ d - 1 := by simpa using hc
  unfold potential
  split_ifs <;> omega

lemma mismatch_subset {v x y : Fin d → ℝ} {j : Fin d}
    (hp : Preserves v j x y) : mismatches v j y ⊆ mismatches v j x := by
  classical
  intro k hk
  have hk' := (Finset.mem_filter.mp hk).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, hk'.1, ?_⟩
  intro h
  exact hk'.2 (hp k hk'.1 h)

lemma mismatch_card_lt {v x y : Fin d → ℝ} {j : Fin d}
    (hp : Preserves v j x y)
    (hit : ∃ k, k ≠ j ∧ x k ≠ v k ∧ y k = v k) :
    (mismatches v j y).card < (mismatches v j x).card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨mismatch_subset hp, ?_⟩
  intro heq
  obtain ⟨k, hkj, hkx, hky⟩ := hit
  have hk : k ∈ mismatches v j x := by simp [mismatches, hkj, hkx]
  rw [← heq] at hk
  exact (Finset.mem_filter.mp hk).2.2 hky

lemma signs_preserved (cap : Fin d → ℝ) (total : ℝ) (x y v : Fin d → ℝ) (j : Fin d)
    (hx : x ∈ slice cap total) (hy : y ∈ slice cap total)
    (hv : ∀ k, k ≠ j → AtBound cap v k) (hp : Preserves v j x y) :
    (Inc v j y → Inc v j x) ∧ (Dec v j y → Dec v j x) := by
  constructor
  · rintro ⟨k, hkj, hki⟩
    have hvc := target_upper_of_inc cap total y v hy (hv k hkj) hki
    refine ⟨k, hkj, ?_⟩
    have hle : x k ≤ v k := by rw [hvc]; exact (hx.1 k).2
    apply lt_of_le_of_ne hle
    intro heq
    have := hp k hkj heq
    linarith
  · rintro ⟨k, hkj, hkd⟩
    have hv0 := target_lower_of_dec cap total y v hy (hv k hkj) hkd
    refine ⟨k, hkj, ?_⟩
    have hle : v k ≤ x k := by rw [hv0]; exact (hx.1 k).1
    apply lt_of_le_of_ne hle
    intro heq
    have := hp k hkj heq.symm
    linarith

lemma potential_drop_hit {cap v x y : Fin d → ℝ} {j : Fin d}
    (hp : Preserves v j x y)
    (hit : ∃ k, k ≠ j ∧ x k ≠ v k ∧ y k = v k)
    (hm : Mixed cap v j y → Mixed cap v j x) :
    potential cap v j y < potential cap v j x := by
  classical
  have hc := mismatch_card_lt hp hit
  unfold potential
  by_cases hx : Mixed cap v j x <;> by_cases hy : Mixed cap v j y
  · simp only [if_pos hx, if_pos hy]; omega
  · simp only [if_pos hx, if_neg hy]; omega
  · exact False.elim (hx (hm hy))
  · simp only [if_neg hx, if_neg hy]; exact hc

lemma potential_drop_break {cap v x y : Fin d → ℝ} {j : Fin d}
    (hp : Preserves v j x y) (hx : Mixed cap v j x) (hy : ¬ Mixed cap v j y) :
    potential cap v j y < potential cap v j x := by
  classical
  have hc := Finset.card_le_card (mismatch_subset hp)
  simp only [potential, if_pos hx, if_neg hy]
  omega

/-- A maximal feasible pivot from a regular point has an extreme endpoint. -/
lemma maximal_exchange_vertex (cap : Fin d → ℝ) (total : ℝ) (x : Fin d → ℝ)
    (p q : Fin d) (hpq : p ≠ q) (hx : x ∈ slice cap total) (hr : Regular cap x)
    (hfixed : ∀ k, k ≠ p → k ≠ q → AtBound cap x k)
    (hpos : 0 < min (cap p - x p) (x q)) :
    let y := exchange x p q (min (cap p - x p) (x q))
    y ∈ extremePoints ℝ (slice cap total) ∧ Adj (slice cap total) x y ∧
      (y p = cap p ∨ y q = 0) := by
  dsimp only
  let ε := min (cap p - x p) (x q)
  let y := exchange x p q ε
  change y ∈ extremePoints ℝ (slice cap total) ∧ Adj (slice cap total) x y ∧ _
  have hp1 : x p < cap p := by have := lt_of_lt_of_le hpos (min_le_left _ _); linarith
  have hq0 : 0 < x q := lt_of_lt_of_le hpos (min_le_right _ _)
  have hstart : x p = 0 ∨ x q = cap q := by
    by_cases hp0 : x p = 0
    · exact Or.inl hp0
    · right
      by_contra hq1
      exact hpq (hr p q ⟨lt_of_le_of_ne (hx.1 p).1 (Ne.symm hp0), hp1⟩
        ⟨hq0, lt_of_le_of_ne (hx.1 q).2 hq1⟩)
  have hy : y ∈ slice cap total :=
    exchange_mem cap total x p q hpq hx ε hpos.le (min_le_left _ _) (min_le_right _ _)
  have hedge : Adj (slice cap total) x y :=
    maximal_exchange_is_edge cap total x p q hpq hx hfixed hstart hpos
  have hf : y p = cap p ∨ y q = 0 := by
    rcases le_total (cap p - x p) (x q) with h | h
    · left
      rw [show y p = x p + ε from exchange_at_p x p q hpq ε]
      dsimp [ε]
      rw [min_eq_left h]
      ring
    · right
      rw [show y q = x q - ε from exchange_at_q x p q hpq ε]
      dsimp [ε]
      rw [min_eq_right h]
      ring
  refine ⟨?_, hedge, hf⟩
  rcases hf with hp | hq
  · apply extreme_of_bound_except cap total y hy q
    intro k hkq
    by_cases hkp : k = p
    · exact Or.inr (by simpa only [hkp] using hp)
    · rw [show y k = x k from exchange_elsewhere x p q k hkp hkq ε]
      exact hfixed k hkp hkq
  · apply extreme_of_bound_except cap total y hy p
    intro k hkp
    by_cases hkq : k = q
    · exact Or.inl (by simpa only [hkq] using hq)
    · rw [show y k = x k from exchange_elsewhere x p q k hkp hkq ε]
      exact hfixed k hkp hkq
end HirschBoxSlice
