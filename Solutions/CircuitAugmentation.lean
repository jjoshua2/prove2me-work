import Mathlib
import Solutions.CircuitSlackBridge
import Solutions.CircuitProgressNumerics

open Set HirschSlack HirschCircuitProgress

set_option maxHeartbeats 5000000

noncomputable section

namespace HirschAugment

variable {n : ℕ}

/-- The minimum positive ratio gives a maximal nonnegative step and an
explicit coordinate that was positive and becomes zero. -/
theorem maximal_nonnegative
    (x g : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i)
    (htangent : ∀ i, x i = 0 → 0 ≤ g i)
    (hneg : ∃ i, g i < 0) :
    ∃ alpha : ℝ, 0 < alpha ∧
      (∀ i, 0 ≤ x i + alpha * g i) ∧
      (∃ q, g q < 0 ∧ 0 < x q ∧ x q + alpha * g q = 0) ∧
      (∀ t : ℝ, alpha < t → ¬ ∀ i, 0 ≤ x i + t * g i) := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun i => g i < 0)
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := hneg
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨q, hq, hmin⟩ := S.exists_min_image (fun i => x i / (-g i)) hS
  have hgq : g q < 0 := (Finset.mem_filter.mp hq).2
  have hxq : 0 < x q := by
    by_contra h
    have hz : x q = 0 := by linarith [hx q]
    have hbad := htangent q hz
    linarith
  let alpha : ℝ := x q / (-g q)
  have ha : 0 < alpha := div_pos hxq (neg_pos.mpr hgq)
  have hlimit : alpha * (-g q) = x q :=
    div_mul_cancel₀ _ (neg_ne_zero.mpr (ne_of_lt hgq))
  have hfeas : ∀ i, 0 ≤ x i + alpha * g i := by
    intro i
    by_cases hgi : g i < 0
    · have hi : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hgi⟩
      have hbound : alpha ≤ x i / (-g i) := hmin i hi
      have hprod := (le_div_iff₀ (neg_pos.mpr hgi)).mp hbound
      nlinarith
    · have hg0 : 0 ≤ g i := le_of_not_gt hgi
      exact add_nonneg (hx i) (mul_nonneg ha.le hg0)
  refine ⟨alpha, ha, hfeas, ⟨q, hgq, hxq, by linarith⟩, ?_⟩
  intro t ht htfeas
  have hqfeas := htfeas q
  nlinarith

lemma support_smul (c : ℝ) (hc : c ≠ 0) (g : Fin n → ℝ) :
    support (c • g) = support g := by
  ext i
  change (c * g i ≠ 0) ↔ (g i ≠ 0)
  simp only [mul_ne_zero_iff, hc, true_and]

lemma elementary_smul
    (K : Submodule ℝ (Fin n → ℝ)) (g : Fin n → ℝ)
    (hg : Elementary K g) (c : ℝ) (hc : c ≠ 0) :
    Elementary K (c • g) := by
  refine ⟨K.smul_mem c hg.1, smul_ne_zero hc hg.2.1, ?_⟩
  intro h hh hne hsub
  have hhsub : support h ⊆ support g := by
    simpa only [support_smul c hc] using hsub
  simpa only [support_smul c hc] using hg.2.2 h hh hne hhsub

/-- An elementary tangent direction with a negative coordinate has a genuine
maximal circuit augmentation. No vertex claim is made about its endpoint. -/
theorem elementary_maximal_step
    (K : Submodule ℝ (Fin n → ℝ)) (b x g : Fin n → ℝ)
    (hx : x ∈ standardSet K b) (hg : Elementary K g)
    (htangent : ∀ i, x i = 0 → 0 ≤ g i)
    (hneg : ∃ i, g i < 0) :
    ∃ alpha : ℝ, 0 < alpha ∧
      StandardStep K b x (x + alpha • g) ∧
      (∃ q, g q < 0 ∧ 0 < x q ∧ (x + alpha • g) q = 0) ∧
      ((∀ i, 0 ≤ x i + g i) → 1 ≤ alpha) := by
  obtain ⟨alpha, ha, hfeas, hhit, hmax⟩ := maximal_nonnegative x g hx.2 htangent hneg
  have hy : x + alpha • g ∈ standardSet K b := by
    refine ⟨?_, ?_⟩
    · have hsum := K.add_mem hx.1 (K.smul_mem alpha hg.1)
      convert hsum using 1 <;> module
    · exact hfeas
  have hdiff : x + alpha • g - x = alpha • g := by abel
  refine ⟨alpha, ha, ⟨hx, hy, ?_, ?_⟩, hhit, ?_⟩
  · rw [hdiff]
    exact elementary_smul K g hg alpha ha.ne'
  · intro t ht hs
    apply hmax (t * alpha) (by nlinarith)
    intro i
    have hi := hs.2 i
    rw [hdiff, smul_smul] at hi
    exact hi
  · intro hunit
    by_contra h
    have halt : alpha < 1 := lt_of_not_ge h
    have hbad := hmax 1 halt
    apply hbad
    simpa only [one_mul] using hunit

/-- A nonnegative support-minimal vector can be found inside the support of
any prescribed nonnegative nonzero vector of a subspace. -/
theorem exists_nonnegative_elementary
    (K : Submodule ℝ (Fin n → ℝ)) (v : Fin n → ℝ)
    (hvK : v ∈ K) (hv0 : v ≠ 0) (hvpos : ∀ i, 0 ≤ v i) :
    ∃ g : Fin n → ℝ, Elementary K g ∧ (∀ i, 0 ≤ g i) ∧ support g ⊆ support v := by
  classical
  let cardSupp : (Fin n → ℝ) → ℕ := fun x =>
    (Finset.univ.filter (fun i => x i ≠ 0)).card
  have hex : ∃ k : ℕ, ∃ g : Fin n → ℝ,
      g ∈ K ∧ g ≠ 0 ∧ (∀ i, 0 ≤ g i) ∧ support g ⊆ support v ∧ cardSupp g = k :=
    ⟨cardSupp v, v, hvK, hv0, hvpos, Set.Subset.rfl, rfl⟩
  obtain ⟨g, hgK, hg0, hgpos, hgsub, hgcard⟩ := Nat.find_spec hex
  have hminimal (z : Fin n → ℝ) (hzK : z ∈ K) (hz0 : z ≠ 0)
      (hzpos : ∀ i, 0 ≤ z i) (hzsub : support z ⊆ support v) :
      cardSupp g ≤ cardSupp z := by
    rw [hgcard]
    exact Nat.find_min' hex ⟨z, hzK, hz0, hzpos, hzsub, rfl⟩
  have no_shrink (h : Fin n → ℝ) (hhK : h ∈ K)
      (hhsub : support h ⊆ support g)
      (hhneg : ∃ i, h i < 0)
      (hmissing : ∃ j, g j ≠ 0 ∧ h j = 0) : False := by
    have htangent : ∀ i, g i = 0 → 0 ≤ h i := by
      intro i hgi
      have hhi : h i = 0 := by
        by_contra hne
        exact (hhsub hne) hgi
      rw [hhi]
    obtain ⟨alpha, ha, hzpos, ⟨q, hhq, hgq, hzq⟩, _⟩ :=
      maximal_nonnegative g h hgpos htangent hhneg
    let z : Fin n → ℝ := g + alpha • h
    have hzK : z ∈ K := K.add_mem hgK (K.smul_mem alpha hhK)
    have hz0 : z ≠ 0 := by
      obtain ⟨j, hgj, hhj⟩ := hmissing
      intro hz
      have hc := congrFun hz j
      change g j + alpha * h j = 0 at hc
      rw [hhj, mul_zero, add_zero] at hc
      exact hgj hc
    have hzsub : support z ⊆ support g := by
      intro i hzi
      by_contra hgi
      have hgi0 : g i = 0 := not_not.mp hgi
      have hhi0 : h i = 0 := by
        by_contra hhi
        exact (hhsub hhi) hgi0
      apply hzi
      change g i + alpha * h i = 0
      rw [hgi0, hhi0, mul_zero, zero_add]
    have hsstrict : (Finset.univ.filter (fun i => z i ≠ 0)) ⊂
        Finset.univ.filter (fun i => g i ≠ 0) := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨?_, ?_⟩
      · intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hzsub (Finset.mem_filter.mp hi).2⟩
      · intro heq
        have hqmem : q ∈ Finset.univ.filter (fun i => g i ≠ 0) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ q, hgq.ne'⟩
        rw [← heq] at hqmem
        exact (Finset.mem_filter.mp hqmem).2 hzq
    have hlt : cardSupp z < cardSupp g := Finset.card_lt_card hsstrict
    have hle := hminimal z hzK hz0 hzpos (hzsub.trans hgsub)
    omega
  refine ⟨g, ⟨hgK, hg0, ?_⟩, hgpos, hgsub⟩
  intro h hhK hh0 hhsub
  by_contra hnot
  have hmissing : ∃ j, g j ≠ 0 ∧ h j = 0 := by
    by_contra h
    apply hnot
    intro j hgj
    by_contra hhj
    exact h ⟨j, hgj, not_not.mp hhj⟩
  by_cases hhneg : ∃ i, h i < 0
  · exact no_shrink h hhK hhsub hhneg hmissing
  · have hnonneg : ∀ i, 0 ≤ h i := fun i => le_of_not_gt (fun hi => hhneg ⟨i, hi⟩)
    have hidx : ∃ i, h i ≠ 0 := by
      by_contra h
      apply hh0
      funext i
      by_contra hi
      exact h ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hidx
    have hpos : 0 < h i := lt_of_le_of_ne (hnonneg i) (Ne.symm hi)
    apply no_shrink (-h) (K.neg_mem hhK)
    · intro j hj
      apply hhsub
      simpa only [Pi.neg_apply, neg_ne_zero] using hj
    · refine ⟨i, ?_⟩
      change -h i < 0
      linarith
    · obtain ⟨j, hgj, hhj⟩ := hmissing
      exact ⟨j, hgj, by simp only [Pi.neg_apply, hhj, neg_zero]⟩

#print axioms maximal_nonnegative
#print axioms elementary_maximal_step
#print axioms exists_nonnegative_elementary

end HirschAugment
