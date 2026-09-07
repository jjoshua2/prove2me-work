import Mathlib
import Solutions.BoxSlicePivotSelection
open Set Hirsch
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace HirschBoxSlice
variable {d : ℕ}

lemma both_pivot (cap : Fin d → ℝ) (total : ℝ) (x v : Fin d → ℝ) (j p q : Fin d)
    (hx : x ∈ extremePoints ℝ (slice cap total))
    (ht : ∀ k, k ≠ j → AtBound cap v k)
    (hpq : p ≠ q) (hpj : p ≠ j) (hqj : q ≠ j)
    (hp : x p < v p) (hq : v q < x q)
    (hfixed : ∀ k, k ≠ p → k ≠ q → AtBound cap x k) :
    ∃ y, y ∈ extremePoints ℝ (slice cap total) ∧ Adj (slice cap total) x y ∧
      potential cap v j y < potential cap v j x := by
  have hvp := target_upper_of_inc cap total x v hx.1 (ht p hpj) hp
  have hvq := target_lower_of_dec cap total x v hx.1 (ht q hqj) hq
  have hpos : 0 < min (cap p - x p) (x q) := by
    apply lt_min
    · rw [← hvp]; exact sub_pos.mpr hp
    · rw [hvq] at hq; exact hq
  let ε := min (cap p - x p) (x q)
  let y := exchange x p q ε
  have hd : y ∈ extremePoints ℝ (slice cap total) ∧ Adj (slice cap total) x y ∧
      (y p = cap p ∨ y q = 0) :=
    maximal_exchange_vertex cap total x p q hpq hx.1 (regular_of_extreme cap total x hx) hfixed hpos
  rcases hd with ⟨hy, hedge, hfinish⟩
  have hpres : Preserves v j x y := exchange_preserves x v j p q ε
    (fun _ => ne_of_lt hp) (fun _ => ne_of_gt hq)
  have hhit : ∃ k, k ≠ j ∧ x k ≠ v k ∧ y k = v k := by
    rcases hfinish with hpf | hqf
    · exact ⟨p, hpj, ne_of_lt hp, hpf.trans hvp.symm⟩
    · exact ⟨q, hqj, ne_of_gt hq, hqf.trans hvq.symm⟩
  have hsigns := signs_preserved cap total x y v j hx.1 hy.1 ht hpres
  have hbuf : y j = x j := exchange_elsewhere x p q j hpj.symm hqj.symm ε
  have hm : Mixed cap v j y → Mixed cap v j x := by
    rintro ⟨hinside, hi, hd⟩
    refine ⟨?_, hsigns.1 hi, hsigns.2 hd⟩
    change 0 < y j ∧ y j < cap j at hinside
    change 0 < x j ∧ x j < cap j
    simpa only [hbuf] using hinside
  exact ⟨y, hy, hedge, potential_drop_hit hpres hhit hm⟩

lemma inc_buffer_pivot (cap : Fin d → ℝ) (total : ℝ) (x v : Fin d → ℝ) (j p : Fin d)
    (hx : x ∈ extremePoints ℝ (slice cap total)) (hv : v ∈ slice cap total)
    (ht : ∀ k, k ≠ j → AtBound cap v k)
    (hpj : p ≠ j) (hp : x p < v p)
    (hfixed : ∀ k, k ≠ p → k ≠ j → AtBound cap x k)
    (hcase : Mixed cap v j x ∨ ¬ Dec v j x) :
    ∃ y, y ∈ extremePoints ℝ (slice cap total) ∧ Adj (slice cap total) x y ∧
      potential cap v j y < potential cap v j x := by
  have hvp := target_upper_of_inc cap total x v hx.1 (ht p hpj) hp
  have hpRoom : 0 < cap p - x p := by rw [← hvp]; exact sub_pos.mpr hp
  have hjMass : 0 < x j := by
    rcases hcase with hm | hn
    · exact hm.1.1
    · exact lt_of_lt_of_le hpRoom (inc_buffer_capacity cap total x v j p hx.1 hv hpj hvp hn)
  have hpos : 0 < min (cap p - x p) (x j) := lt_min hpRoom hjMass
  let ε := min (cap p - x p) (x j)
  let y := exchange x p j ε
  have hd : y ∈ extremePoints ℝ (slice cap total) ∧ Adj (slice cap total) x y ∧
      (y p = cap p ∨ y j = 0) :=
    maximal_exchange_vertex cap total x p j hpj hx.1 (regular_of_extreme cap total x hx) hfixed hpos
  rcases hd with ⟨hy, hedge, hfinish⟩
  have hpres : Preserves v j x y := exchange_preserves x v j p j ε
    (fun _ => ne_of_lt hp) (fun h => False.elim (h rfl))
  refine ⟨y, hy, hedge, ?_⟩
  rcases hcase with hm | hn
  · rcases hfinish with hpf | hjf
    · have hhit : ∃ k, k ≠ j ∧ x k ≠ v k ∧ y k = v k :=
        ⟨p, hpj, ne_of_lt hp, hpf.trans hvp.symm⟩
      exact potential_drop_hit hpres hhit (fun _ => hm)
    · apply potential_drop_break hpres hm
      intro hym
      have h0 : 0 < y j := hym.1.1
      rw [hjf] at h0
      exact (lt_irrefl 0) h0
  · have hcap := inc_buffer_capacity cap total x v j p hx.1 hv hpj hvp hn
    have hpf : y p = v p := by
      rw [show y p = x p + ε from exchange_at_p x p j hpj ε]
      dsimp [ε]
      rw [min_eq_left hcap]
      linarith
    have hsigns := signs_preserved cap total x y v j hx.1 hy.1 ht hpres
    have hnot : ¬ Mixed cap v j y := fun hym => hn (hsigns.2 hym.2.2)
    exact potential_drop_hit hpres ⟨p, hpj, ne_of_lt hp, hpf⟩
      (fun hym => False.elim (hnot hym))

lemma dec_buffer_pivot (cap : Fin d → ℝ) (total : ℝ) (x v : Fin d → ℝ) (j q : Fin d)
    (hx : x ∈ extremePoints ℝ (slice cap total)) (hv : v ∈ slice cap total)
    (ht : ∀ k, k ≠ j → AtBound cap v k)
    (hqj : q ≠ j) (hq : v q < x q)
    (hfixed : ∀ k, k ≠ j → k ≠ q → AtBound cap x k)
    (hcase : Mixed cap v j x ∨ ¬ Inc v j x) :
    ∃ y, y ∈ extremePoints ℝ (slice cap total) ∧ Adj (slice cap total) x y ∧
      potential cap v j y < potential cap v j x := by
  have hvq := target_lower_of_dec cap total x v hx.1 (ht q hqj) hq
  have hqMass : 0 < x q := by rw [hvq] at hq; exact hq
  have hjRoom : 0 < cap j - x j := by
    rcases hcase with hm | hn
    · exact sub_pos.mpr hm.1.2
    · exact lt_of_lt_of_le hqMass (dec_buffer_capacity cap total x v j q hx.1 hv hqj hvq hn)
  have hpos : 0 < min (cap j - x j) (x q) := lt_min hjRoom hqMass
  let ε := min (cap j - x j) (x q)
  let y := exchange x j q ε
  have hd : y ∈ extremePoints ℝ (slice cap total) ∧ Adj (slice cap total) x y ∧
      (y j = cap j ∨ y q = 0) :=
    maximal_exchange_vertex cap total x j q hqj.symm hx.1 (regular_of_extreme cap total x hx) hfixed hpos
  rcases hd with ⟨hy, hedge, hfinish⟩
  have hpres : Preserves v j x y := exchange_preserves x v j j q ε
    (fun h => False.elim (h rfl)) (fun _ => ne_of_gt hq)
  refine ⟨y, hy, hedge, ?_⟩
  rcases hcase with hm | hn
  · rcases hfinish with hjf | hqf
    · apply potential_drop_break hpres hm
      intro hym
      have h1 : y j < cap j := hym.1.2
      rw [hjf] at h1
      exact (lt_irrefl _) h1
    · have hhit : ∃ k, k ≠ j ∧ x k ≠ v k ∧ y k = v k :=
        ⟨q, hqj, ne_of_gt hq, hqf.trans hvq.symm⟩
      exact potential_drop_hit hpres hhit (fun _ => hm)
  · have hcap := dec_buffer_capacity cap total x v j q hx.1 hv hqj hvq hn
    have hqf : y q = v q := by
      rw [show y q = x q - ε from exchange_at_q x j q hqj.symm ε]
      dsimp [ε]
      rw [min_eq_right hcap]
      linarith
    have hsigns := signs_preserved cap total x y v j hx.1 hy.1 ht hpres
    have hnot : ¬ Mixed cap v j y := fun hym => hn (hsigns.1 hym.2.1)
    exact potential_drop_hit hpres ⟨q, hqj, ne_of_gt hq, hqf⟩
      (fun hym => False.elim (hnot hym))

/-- Concrete pivot existence: every nonterminal vertex has an actual edge
to an extreme point of strictly smaller mismatch-plus-mixed-buffer potential.
The target buffer coordinate may itself be at a bound. -/
theorem decreasing_pivot (cap : Fin d → ℝ) (total : ℝ) (v : Fin d → ℝ) (j : Fin d)
    (hv : v ∈ slice cap total) (ht : ∀ k, k ≠ j → AtBound cap v k)
    (x : Fin d → ℝ) (hx : x ∈ extremePoints ℝ (slice cap total)) (hne : x ≠ v) :
    ∃ y, y ∈ extremePoints ℝ (slice cap total) ∧ Adj (slice cap total) x y ∧
      potential cap v j y < potential cap v j x := by
  classical
  have hr := regular_of_extreme cap total x hx
  by_cases hi : Inc v j x
  · by_cases hd : Dec v j x
    · by_cases hj : Inside cap x j
      · obtain ⟨p, hpj, hp⟩ := hi
        have hfixed : ∀ k, k ≠ p → k ≠ j → AtBound cap x k := by
          intro k hkp hkj
          exact bounds_except_inside cap total x hx.1 hr j hj k hkj
        exact inc_buffer_pivot cap total x v j p hx hv ht hpj hp hfixed
          (Or.inl ⟨hj, ⟨p, hpj, hp⟩, hd⟩)
      · obtain ⟨p, q, hpq, hpj, hqj, hp, hq, hfixed⟩ :=
          select_both cap total x v j hx.1 hr ht (bound_of_not_inside cap total x hx.1 j hj) hi hd
        exact both_pivot cap total x v j p q hx ht hpq hpj hqj hp hq hfixed
    · obtain ⟨p, hpj, hp, hfixed⟩ := select_inc_buffer cap total x v j hx.1 hr ht hi hd
      exact inc_buffer_pivot cap total x v j p hx hv ht hpj hp hfixed (Or.inr hd)
  · by_cases hd : Dec v j x
    · obtain ⟨q, hqj, hq, hfixed⟩ := select_dec_buffer cap total x v j hx.1 hr ht hi hd
      exact dec_buffer_pivot cap total x v j q hx hv ht hqj hq hfixed (Or.inr hi)
    · exact False.elim (hne (eq_of_no_signs total cap x v j hx.1 hv hi hd))
end HirschBoxSlice
#print axioms HirschBoxSlice.decreasing_pivot
