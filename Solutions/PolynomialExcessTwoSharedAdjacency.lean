import Mathlib
import Solutions.PolynomialExcessTwoConvexity

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 5000000
set_option autoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschExcessTwo

/-- A finite sum supported on three distinct indices reduces to those three
terms. -/
lemma sum_eq_add_add_of_zero_off_triple {n : ℕ}
    (f : Fin n → ℝ) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hzero : ∀ r, r ≠ i → r ≠ j → r ≠ k → f r = 0) :
    (∑ r, f r) = f i + f j + f k := by
  classical
  have hsub : ({i, j, k} : Finset (Fin n)) ⊆ Finset.univ := by simp
  have hsmall :
      (∑ r ∈ ({i, j, k} : Finset (Fin n)), f r) =
        ∑ r ∈ (Finset.univ : Finset (Fin n)), f r := by
    apply Finset.sum_subset hsub
    intro r _ hr
    apply hzero r
    · intro hri
      subst r
      exact hr (by simp)
    · intro hrj
      subst r
      exact hr (by simp)
    · intro hrk
      subst r
      exact hr (by simp)
  calc
    (∑ r, f r) = ∑ r ∈ (Finset.univ : Finset (Fin n)), f r := rfl
    _ = ∑ r ∈ ({i, j, k} : Finset (Fin n)), f r := hsmall.symm
    _ = f i + f j + f k := by
      simp [hij, hik, hjk, add_comm, add_left_comm]

/-- With one low index and two distinct high indices, the corresponding
three-coordinate support face is exactly the segment joining the two pair
vertices. -/
theorem supportFace_triple_eq_segment_shared_low {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j k : Fin n)
    (hli : t i < mu) (hrj : mu < t j) (hrk : mu < t k)
    (hjk : j ≠ k) :
    supportFace t mu {i, j, k} =
      segment ℝ (pairPoint t mu i j) (pairPoint t mu i k) := by
  classical
  have hij : i ≠ j := by
    intro h
    subst j
    linarith
  have hik : i ≠ k := by
    intro h
    subst k
    linarith
  have hji : j ≠ i := hij.symm
  have hki : k ≠ i := hik.symm
  have hkj : k ≠ j := hjk.symm
  have hdj : 0 < t j - t i := by linarith
  have hdk : 0 < t k - t i := by linarith
  have hD : 0 < mu - t i := by linarith
  apply Set.Subset.antisymm
  · intro s hs
    have hzero : ∀ r, r ≠ i → r ≠ j → r ≠ k → s r = 0 := by
      intro r hri hrj' hrk'
      exact hs.2 r (by simp [hri, hrj', hrk'])
    have hmassSum := sum_eq_add_add_of_zero_off_triple
      (fun r => s r) i j k hij hik hjk hzero
    have hmass : s i + s j + s k = 1 := by
      calc
        s i + s j + s k = ∑ r, s r := hmassSum.symm
        _ = 1 := hs.1.2.1
    have hmomSum := sum_eq_add_add_of_zero_off_triple
      (fun r => t r * s r) i j k hij hik hjk (by
        intro r hri hrj' hrk'
        change t r * s r = 0
        rw [hzero r hri hrj' hrk', mul_zero])
    have hmom : t i * s i + t j * s j + t k * s k = mu := by
      calc
        t i * s i + t j * s j + t k * s k = ∑ r, t r * s r := hmomSum.symm
        _ = mu := hs.1.2.2
    let A : ℝ := (t j - t i) * s j
    let B : ℝ := (t k - t i) * s k
    have hA : 0 ≤ A := by
      dsimp [A]
      exact mul_nonneg hdj.le (hs.1.1 j)
    have hB : 0 ≤ B := by
      dsimp [B]
      exact mul_nonneg hdk.le (hs.1.1 k)
    have hAB : A + B = mu - t i := by
      dsimp [A, B]
      linear_combination hmom - (t i) * hmass
    have hABpos : 0 < A + B := by rw [hAB]; exact hD
    have hα : 0 ≤ A / (A + B) := div_nonneg hA hABpos.le
    have hβ : 0 ≤ B / (A + B) := div_nonneg hB hABpos.le
    have hαβ : A / (A + B) + B / (A + B) = 1 := by
      rw [← add_div, div_self (ne_of_gt hABpos)]
    have hp : pairPoint t mu i j ∈ momentSlice t mu := pairPoint_mem t mu i j hli hrj
    have hq : pairPoint t mu i k ∈ momentSlice t mu := pairPoint_mem t mu i k hli hrk
    let v : EuclideanSpace ℝ (Fin n) :=
      (A / (A + B)) • pairPoint t mu i j +
        (B / (A + B)) • pairPoint t mu i k
    have hvP : v ∈ momentSlice t mu := by
      dsimp [v]
      exact (momentSlice_convex t mu) hp hq hα hβ hαβ
    have hvj : v j = s j := by
      dsimp [v]
      change
        (A / (A + B)) * pairPoint t mu i j j +
          (B / (A + B)) * pairPoint t mu i k j = s j
      rw [pairPoint_apply_right t mu i j hij,
        pairPoint_apply_other t mu i k j hji hjk, mul_zero, add_zero, hAB]
      dsimp [A]
      field_simp [ne_of_gt hD, ne_of_gt hdj]
    have hvk : v k = s k := by
      dsimp [v]
      change
        (A / (A + B)) * pairPoint t mu i j k +
          (B / (A + B)) * pairPoint t mu i k k = s k
      rw [pairPoint_apply_other t mu i j k hki hkj,
        pairPoint_apply_right t mu i k hik, mul_zero, zero_add, hAB]
      dsimp [B]
      field_simp [ne_of_gt hD, ne_of_gt hdk]
    have hvzero : ∀ r, r ≠ i → r ≠ j → r ≠ k → v r = 0 := by
      intro r hri hrj' hrk'
      dsimp [v]
      change
        (A / (A + B)) * pairPoint t mu i j r +
          (B / (A + B)) * pairPoint t mu i k r = 0
      rw [pairPoint_apply_other t mu i j r hri hrj',
        pairPoint_apply_other t mu i k r hri hrk']
      ring
    have hvmassSum := sum_eq_add_add_of_zero_off_triple
      (fun r => v r) i j k hij hik hjk hvzero
    have hvmass : v i + v j + v k = 1 := by
      calc
        v i + v j + v k = ∑ r, v r := hvmassSum.symm
        _ = 1 := hvP.2.1
    have hvi : v i = s i := by
      nlinarith [hvmass, hmass, hvj, hvk]
    refine mem_segment_iff_div.mpr ⟨A, B, hA, hB, hABpos, ?_⟩
    change v = s
    ext r
    by_cases hri : r = i
    · subst r
      exact hvi
    · by_cases hrj' : r = j
      · subst r
        exact hvj
      · by_cases hrk' : r = k
        · subst r
          exact hvk
        · exact (hvzero r hri hrj' hrk').trans (hzero r hri hrj' hrk').symm
  · intro s hs
    have hpS : pairPoint t mu i j ∈ supportFace t mu {i, j, k} :=
      pairPoint_mem_supportFace t mu i j hli hrj {i, j, k} (by simp) (by simp)
    have hqS : pairPoint t mu i k ∈ supportFace t mu {i, j, k} :=
      pairPoint_mem_supportFace t mu i k hli hrk {i, j, k} (by simp) (by simp)
    exact segment_subset_supportFace t mu {i, j, k}
      (pairPoint t mu i j) (pairPoint t mu i k) hpS hqS hs

/-- Pair vertices sharing a low index are adjacent. -/
theorem pairPoint_adj_shared_low {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j k : Fin n)
    (hli : t i < mu) (hrj : mu < t j) (hrk : mu < t k)
    (hjk : j ≠ k) :
    Adj (momentSlice t mu) (pairPoint t mu i j) (pairPoint t mu i k) := by
  classical
  have hij : i ≠ j := by intro h; subst j; linarith
  have hik : i ≠ k := by intro h; subst k; linarith
  have hji : j ≠ i := hij.symm
  have hne : pairPoint t mu i j ≠ pairPoint t mu i k := by
    intro h
    have hc := congrArg (fun s : EuclideanSpace ℝ (Fin n) => s j) h
    change pairPoint t mu i j j = pairPoint t mu i k j at hc
    rw [pairPoint_apply_right t mu i j hij,
      pairPoint_apply_other t mu i k j hji hjk] at hc
    have hp : 0 < (mu - t i) / (t j - t i) := by
      exact div_pos (sub_pos.mpr hli) (sub_pos.mpr (hli.trans hrj))
    linarith
  refine ⟨hne, ?_⟩
  rw [← supportFace_triple_eq_segment_shared_low t mu i j k hli hrj hrk hjk]
  exact supportFace_isExtreme t mu {i, j, k}

/-- With two distinct low indices and one high index, the corresponding
three-coordinate support face is exactly the segment joining the two pair
vertices. -/
theorem supportFace_triple_eq_segment_shared_high {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j k : Fin n)
    (hli : t i < mu) (hlj : t j < mu) (hrk : mu < t k)
    (hij : i ≠ j) :
    supportFace t mu {i, j, k} =
      segment ℝ (pairPoint t mu i k) (pairPoint t mu j k) := by
  classical
  have hik : i ≠ k := by
    intro h
    subst k
    linarith
  have hjk : j ≠ k := by
    intro h
    subst k
    linarith
  have hji : j ≠ i := hij.symm
  have hki : k ≠ i := hik.symm
  have hkj : k ≠ j := hjk.symm
  have hdi : 0 < t k - t i := by linarith
  have hdj : 0 < t k - t j := by linarith
  have hD : 0 < t k - mu := by linarith
  apply Set.Subset.antisymm
  · intro s hs
    have hzero : ∀ r, r ≠ i → r ≠ j → r ≠ k → s r = 0 := by
      intro r hri hrj' hrk'
      exact hs.2 r (by simp [hri, hrj', hrk'])
    have hmassSum := sum_eq_add_add_of_zero_off_triple
      (fun r => s r) i j k hij hik hjk hzero
    have hmass : s i + s j + s k = 1 := by
      calc
        s i + s j + s k = ∑ r, s r := hmassSum.symm
        _ = 1 := hs.1.2.1
    have hmomSum := sum_eq_add_add_of_zero_off_triple
      (fun r => t r * s r) i j k hij hik hjk (by
        intro r hri hrj' hrk'
        change t r * s r = 0
        rw [hzero r hri hrj' hrk', mul_zero])
    have hmom : t i * s i + t j * s j + t k * s k = mu := by
      calc
        t i * s i + t j * s j + t k * s k = ∑ r, t r * s r := hmomSum.symm
        _ = mu := hs.1.2.2
    let A : ℝ := (t k - t i) * s i
    let B : ℝ := (t k - t j) * s j
    have hA : 0 ≤ A := by
      dsimp [A]
      exact mul_nonneg hdi.le (hs.1.1 i)
    have hB : 0 ≤ B := by
      dsimp [B]
      exact mul_nonneg hdj.le (hs.1.1 j)
    have hAB : A + B = t k - mu := by
      dsimp [A, B]
      linear_combination (t k) * hmass - hmom
    have hABpos : 0 < A + B := by rw [hAB]; exact hD
    have hα : 0 ≤ A / (A + B) := div_nonneg hA hABpos.le
    have hβ : 0 ≤ B / (A + B) := div_nonneg hB hABpos.le
    have hαβ : A / (A + B) + B / (A + B) = 1 := by
      rw [← add_div, div_self (ne_of_gt hABpos)]
    have hp : pairPoint t mu i k ∈ momentSlice t mu := pairPoint_mem t mu i k hli hrk
    have hq : pairPoint t mu j k ∈ momentSlice t mu := pairPoint_mem t mu j k hlj hrk
    let v : EuclideanSpace ℝ (Fin n) :=
      (A / (A + B)) • pairPoint t mu i k +
        (B / (A + B)) • pairPoint t mu j k
    have hvP : v ∈ momentSlice t mu := by
      dsimp [v]
      exact (momentSlice_convex t mu) hp hq hα hβ hαβ
    have hvi : v i = s i := by
      dsimp [v]
      change
        (A / (A + B)) * pairPoint t mu i k i +
          (B / (A + B)) * pairPoint t mu j k i = s i
      rw [pairPoint_apply_left,
        pairPoint_apply_other t mu j k i hij hik, mul_zero, add_zero, hAB]
      dsimp [A]
      field_simp [ne_of_gt hD, ne_of_gt hdi]
    have hvj : v j = s j := by
      dsimp [v]
      change
        (A / (A + B)) * pairPoint t mu i k j +
          (B / (A + B)) * pairPoint t mu j k j = s j
      rw [pairPoint_apply_other t mu i k j hji hjk,
        pairPoint_apply_left, mul_zero, zero_add, hAB]
      dsimp [B]
      field_simp [ne_of_gt hD, ne_of_gt hdj]
    have hvzero : ∀ r, r ≠ i → r ≠ j → r ≠ k → v r = 0 := by
      intro r hri hrj' hrk'
      dsimp [v]
      change
        (A / (A + B)) * pairPoint t mu i k r +
          (B / (A + B)) * pairPoint t mu j k r = 0
      rw [pairPoint_apply_other t mu i k r hri hrk',
        pairPoint_apply_other t mu j k r hrj' hrk']
      ring
    have hvmassSum := sum_eq_add_add_of_zero_off_triple
      (fun r => v r) i j k hij hik hjk hvzero
    have hvmass : v i + v j + v k = 1 := by
      calc
        v i + v j + v k = ∑ r, v r := hvmassSum.symm
        _ = 1 := hvP.2.1
    have hvk : v k = s k := by
      nlinarith [hvmass, hmass, hvi, hvj]
    refine mem_segment_iff_div.mpr ⟨A, B, hA, hB, hABpos, ?_⟩
    change v = s
    ext r
    by_cases hri : r = i
    · subst r
      exact hvi
    · by_cases hrj' : r = j
      · subst r
        exact hvj
      · by_cases hrk' : r = k
        · subst r
          exact hvk
        · exact (hvzero r hri hrj' hrk').trans (hzero r hri hrj' hrk').symm
  · intro s hs
    have hpS : pairPoint t mu i k ∈ supportFace t mu {i, j, k} :=
      pairPoint_mem_supportFace t mu i k hli hrk {i, j, k} (by simp) (by simp)
    have hqS : pairPoint t mu j k ∈ supportFace t mu {i, j, k} :=
      pairPoint_mem_supportFace t mu j k hlj hrk {i, j, k} (by simp) (by simp)
    exact segment_subset_supportFace t mu {i, j, k}
      (pairPoint t mu i k) (pairPoint t mu j k) hpS hqS hs

/-- Pair vertices sharing a high index are adjacent. -/
theorem pairPoint_adj_shared_high {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j k : Fin n)
    (hli : t i < mu) (hlj : t j < mu) (hrk : mu < t k)
    (hij : i ≠ j) :
    Adj (momentSlice t mu) (pairPoint t mu i k) (pairPoint t mu j k) := by
  classical
  have hik : i ≠ k := by intro h; subst k; linarith
  have hne : pairPoint t mu i k ≠ pairPoint t mu j k := by
    intro h
    have hc := congrArg (fun s : EuclideanSpace ℝ (Fin n) => s i) h
    change pairPoint t mu i k i = pairPoint t mu j k i at hc
    rw [pairPoint_apply_left,
      pairPoint_apply_other t mu j k i hij hik] at hc
    have hp : 0 < (t k - mu) / (t k - t i) := by
      exact div_pos (sub_pos.mpr hrk) (sub_pos.mpr (hli.trans hrk))
    linarith
  refine ⟨hne, ?_⟩
  rw [← supportFace_triple_eq_segment_shared_high t mu i j k hli hlj hrk hij]
  exact supportFace_isExtreme t mu {i, j, k}

/-- Any two low/high pair vertices have a canonical route of at most two
edge/stay steps through the cross pair using the first low and second high
index. -/
theorem pairPoint_two_step_route {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ)
    (i k j l : Fin n)
    (hli : t i < mu) (hlk : t k < mu)
    (hrj : mu < t j) (hrl : mu < t l) :
    (pairPoint t mu i j = pairPoint t mu i l ∨
      Adj (momentSlice t mu) (pairPoint t mu i j) (pairPoint t mu i l)) ∧
    (pairPoint t mu i l = pairPoint t mu k l ∨
      Adj (momentSlice t mu) (pairPoint t mu i l) (pairPoint t mu k l)) := by
  constructor
  · by_cases hjl : j = l
    · left
      subst l
      rfl
    · right
      exact pairPoint_adj_shared_low t mu i j l hli hrj hrl hjl
  · by_cases hik : i = k
    · left
      subst k
      rfl
    · right
      exact pairPoint_adj_shared_high t mu i k l hli hlk hrl hik

#print axioms sum_eq_add_add_of_zero_off_triple
#print axioms supportFace_triple_eq_segment_shared_low
#print axioms pairPoint_adj_shared_low
#print axioms supportFace_triple_eq_segment_shared_high
#print axioms pairPoint_adj_shared_high
#print axioms pairPoint_two_step_route

end HirschExcessTwo
