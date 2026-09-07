import Mathlib
import Definitions.Def_Hirsch_model

open Set Hirsch
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HirschBoxSlice
variable {d : ℕ}

def slice (cap : Fin d → ℝ) (total : ℝ) : Set (Fin d → ℝ) :=
  {x | (∀ k, 0 ≤ x k ∧ x k ≤ cap k) ∧ ∑ k, x k = total}

def exchange (x : Fin d → ℝ) (p q : Fin d) (ε : ℝ) : Fin d → ℝ :=
  fun k => x k + (if k = p then ε else 0) - (if k = q then ε else 0)

lemma exchange_at_p (x : Fin d → ℝ) (p q : Fin d) (hpq : p ≠ q) (ε : ℝ) :
    exchange x p q ε p = x p + ε := by simp [exchange, hpq]
lemma exchange_at_q (x : Fin d → ℝ) (p q : Fin d) (hpq : p ≠ q) (ε : ℝ) :
    exchange x p q ε q = x q - ε := by simp [exchange, hpq.symm]
lemma exchange_elsewhere (x : Fin d → ℝ) (p q k : Fin d)
    (hkp : k ≠ p) (hkq : k ≠ q) (ε : ℝ) :
    exchange x p q ε k = x k := by simp [exchange, hkp, hkq]
lemma exchange_sum (x : Fin d → ℝ) (p q : Fin d) (ε : ℝ) :
    (∑ k, exchange x p q ε k) = ∑ k, x k := by
  simp [exchange, Finset.sum_sub_distrib, Finset.sum_add_distrib]

lemma exchange_mem (cap : Fin d → ℝ) (total : ℝ)
    (x : Fin d → ℝ) (p q : Fin d) (hpq : p ≠ q)
    (hx : x ∈ slice cap total) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hεp : ε ≤ cap p - x p) (hεq : ε ≤ x q) :
    exchange x p q ε ∈ slice cap total := by
  refine ⟨?_, (exchange_sum x p q ε).trans hx.2⟩
  intro k
  by_cases hkp : k = p
  · subst k
    rw [exchange_at_p x p q hpq ε]
    constructor <;> linarith [(hx.1 p).1, (hx.1 p).2]
  · by_cases hkq : k = q
    · subst k
      rw [exchange_at_q x p q hpq ε]
      constructor <;> linarith [(hx.1 q).1, (hx.1 q).2]
    · rw [exchange_elsewhere x p q k hkp hkq ε]
      exact hx.1 k

lemma two_coordinate_sum (x z : Fin d → ℝ) (p q : Fin d) (hpq : p ≠ q)
    (hsum : (∑ k, z k) = ∑ k, x k)
    (hother : ∀ k, k ≠ p → k ≠ q → z k = x k) :
    z p + z q = x p + x q := by
  classical
  let S : Finset (Fin d) := Finset.univ.erase p
  have hqS : q ∈ S := by simp [S, hpq.symm]
  have hx1 := Finset.sum_erase_add Finset.univ x (Finset.mem_univ p)
  have hz1 := Finset.sum_erase_add Finset.univ z (Finset.mem_univ p)
  have hx2 := Finset.sum_erase_add S x hqS
  have hz2 := Finset.sum_erase_add S z hqS
  have hrest : (∑ k ∈ S.erase q, z k) = ∑ k ∈ S.erase q, x k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hne : k ≠ q ∧ k ≠ p := by simpa [S] using hk
    exact hother k hne.2 hne.1
  dsimp [S] at hx2 hz2 hrest
  linarith

/-- A maximal two-coordinate transfer is an actual edge, not only a circuit. -/
lemma maximal_exchange_is_edge
    (cap : Fin d → ℝ) (total : ℝ) (x : Fin d → ℝ)
    (p q : Fin d) (hpq : p ≠ q) (hx : x ∈ slice cap total)
    (hfixed : ∀ k, k ≠ p → k ≠ q → x k = 0 ∨ x k = cap k)
    (hstart : x p = 0 ∨ x q = cap q)
    (hpositive : 0 < min (cap p - x p) (x q)) :
    Adj (slice cap total) x (exchange x p q (min (cap p - x p) (x q))) := by
  classical
  let ε : ℝ := min (cap p - x p) (x q)
  let y := exchange x p q ε
  have hε : 0 < ε := hpositive
  have hyp : y p = x p + ε := exchange_at_p x p q hpq ε
  have hyq : y q = x q - ε := exchange_at_q x p q hpq ε
  have hyo : ∀ k, k ≠ p → k ≠ q → y k = x k := by
    intro k hkp hkq
    exact exchange_elsewhere x p q k hkp hkq ε
  have hy : y ∈ slice cap total :=
    exchange_mem cap total x p q hpq hx ε hε.le (min_le_left _ _) (min_le_right _ _)
  have hfinish : y p = cap p ∨ y q = 0 := by
    rcases le_total (cap p - x p) (x q) with h | h
    · have heq : ε = cap p - x p := min_eq_left h
      exact Or.inl (by rw [hyp, heq]; ring)
    · have heq : ε = x q := min_eq_right h
      exact Or.inr (by rw [hyq, heq]; ring)
  let F : Set (Fin d → ℝ) :=
    {z | z ∈ slice cap total ∧ ∀ k, k ≠ p → k ≠ q → z k = x k}
  have hFext : IsExtreme ℝ (slice cap total) F := by
    refine ⟨fun z hz => hz.1, ?_⟩
    intro r hr s hs z hz hopen
    refine ⟨hr, ?_⟩
    intro k hkp hkq
    obtain ⟨α, β, hα, hβ, hαβ, hcombo⟩ := hopen
    have hcoord := congrFun hcombo k
    change α * r k + β * s k = z k at hcoord
    have hpin : z k = x k := hz.2 k hkp hkq
    rw [hpin] at hcoord
    rcases hfixed k hkp hkq with hk0 | hkcap
    · rw [hk0] at hcoord ⊢
      have hr0 := (hr.1 k).1
      have hs0 := (hs.1 k).1
      by_contra hrne
      have hrpos : 0 < r k := lt_of_le_of_ne hr0 (Ne.symm hrne)
      have hprod := mul_pos hα hrpos
      linarith [mul_nonneg hβ.le hs0]
    · rw [hkcap] at hcoord ⊢
      have hrle := (hr.1 k).2
      have hsle := (hs.1 k).2
      have hweight : α * cap k + β * cap k = cap k := by rw [← add_mul, hαβ, one_mul]
      by_contra hrne
      have hrlt : r k < cap k := lt_of_le_of_ne hrle hrne
      have hprod := mul_pos hα (sub_pos.mpr hrlt)
      nlinarith [mul_nonneg hβ.le (sub_nonneg.mpr hsle)]
  have hFsub : F ⊆ segment ℝ x y := by
    intro z hz
    have hsum : z p + z q = x p + x q :=
      two_coordinate_sum x z p q hpq (hz.1.2.trans hx.2.symm) hz.2
    let t : ℝ := (z p - x p) / ε
    have hzp : z p = x p + t * ε := by
      dsimp [t]
      rw [div_mul_cancel₀ _ hε.ne']
      ring
    have hzq : z q = x q - t * ε := by linarith
    have ht0 : 0 ≤ t := by
      by_contra ht
      have htneg : t < 0 := lt_of_not_ge ht
      have hmul : t * ε < 0 := mul_neg_of_neg_of_pos htneg hε
      rcases hstart with hp0 | hqc
      · have hzlo := (hz.1.1 p).1
        rw [hp0] at hzp
        nlinarith
      · have hzhi := (hz.1.1 q).2
        rw [hqc] at hzq
        nlinarith
    have ht1 : t ≤ 1 := by
      by_contra ht
      have htgt : 1 < t := lt_of_not_ge ht
      have hmul := mul_pos (sub_pos.mpr htgt) hε
      rcases hfinish with hpc | hq0
      · have hzhi := (hz.1.1 p).2
        rw [hyp] at hpc
        nlinarith
      · have hzlo := (hz.1.1 q).1
        rw [hyq] at hq0
        nlinarith
    refine ⟨1 - t, t, sub_nonneg.mpr ht1, ht0, by ring, ?_⟩
    funext k
    change (1 - t) * x k + t * y k = z k
    by_cases hkp : k = p
    · subst k
      rw [hyp, hzp]
      ring
    · by_cases hkq : k = q
      · subst k
        rw [hyq, hzq]
        ring
      · rw [hyo k hkp hkq, hz.2 k hkp hkq]
        ring
  have hsegF : segment ℝ x y ⊆ F := by
    intro z hz
    obtain ⟨α, β, hα, hβ, hαβ, hcombo⟩ := hz
    have hcoord : ∀ k, z k = α * x k + β * y k := by
      intro k
      exact (congrFun hcombo k).symm
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro k
      rw [hcoord k]
      constructor
      · exact add_nonneg (mul_nonneg hα (hx.1 k).1) (mul_nonneg hβ (hy.1 k).1)
      · calc
          α * x k + β * y k ≤ α * cap k + β * cap k :=
            add_le_add (mul_le_mul_of_nonneg_left (hx.1 k).2 hα)
              (mul_le_mul_of_nonneg_left (hy.1 k).2 hβ)
          _ = cap k := by rw [← add_mul, hαβ, one_mul]
    · rw [← hcombo]
      change (∑ k, α * x k + β * y k) = total
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        hx.2, hy.2, ← add_mul, hαβ, one_mul]
    · intro k hkp hkq
      rw [hcoord k, hyo k hkp hkq, ← add_mul, hαβ, one_mul]
  have hne : x ≠ y := by
    intro heq
    have h := congrFun heq p
    rw [hyp] at h
    linarith
  have hFeq : F = segment ℝ x y := Set.Subset.antisymm hFsub hsegF
  exact ⟨hne, hFeq ▸ hFext⟩
end HirschBoxSlice
#print axioms HirschBoxSlice.maximal_exchange_is_edge
