import Mathlib
import Solutions.PolynomialExcessTwoVertexClassification
import Solutions.PolynomialExcessTwoSharedAdjacency

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 3000000
set_option autoImplicit false

noncomputable section

namespace HirschExcessTwo

lemma singletonPoint_mem_supportFace {n : ℕ} (t : Fin n → ℝ) (mu : ℝ)
    (i : Fin n) (hi : t i = mu) (S : Finset (Fin n)) (hiS : i ∈ S) :
    singletonPoint i ∈ supportFace t mu S := by
  classical
  refine ⟨singletonPoint_mem t mu i hi, ?_⟩
  intro k hk
  have hki : k ≠ i := by intro h; subst k; exact hk hiS
  simp [singletonPoint_apply, hki]

/-- The carrier of two distinct equal-moment singleton vertices is their edge. -/
theorem supportFace_pair_eq_segment_singletons {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j : Fin n)
    (hi : t i = mu) (hj : t j = mu) (hij : i ≠ j) :
    supportFace t mu {i, j} = segment ℝ (singletonPoint i) (singletonPoint j) := by
  classical
  apply Set.Subset.antisymm
  · intro s hs
    have hzero : ∀ k, k ≠ i → k ≠ j → s k = 0 := by
      intro k hki hkj
      exact hs.2 k (by simp [hki, hkj])
    have hsum := sum_eq_add_of_zero_off_pair (fun k => s k) i j hij hzero
    have hmass : s i + s j = 1 := hsum.symm.trans hs.1.2.1
    refine mem_segment_iff_div.mpr ⟨s i, s j, hs.1.1 i, hs.1.1 j,
      by rw [hmass]; norm_num, ?_⟩
    ext k
    change s i / (s i + s j) * singletonPoint i k +
      s j / (s i + s j) * singletonPoint j k = s k
    rw [hmass]
    by_cases hki : k = i
    · subst k
      simp [singletonPoint_apply, hij]
    · by_cases hkj : k = j
      · subst k
        simp [singletonPoint_apply, hij.symm]
      · simp [singletonPoint_apply, hki, hkj, hzero k hki hkj]
  · exact segment_subset_supportFace t mu {i, j} _ _
      (singletonPoint_mem_supportFace t mu i hi {i, j} (by simp))
      (singletonPoint_mem_supportFace t mu j hj {i, j} (by simp))

theorem singletonPoint_adj_singletonPoint {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j : Fin n)
    (hi : t i = mu) (hj : t j = mu) (hij : i ≠ j) :
    Adj (momentSlice t mu) (singletonPoint i) (singletonPoint j) := by
  classical
  refine ⟨?_, ?_⟩
  · intro h
    have hc := congrArg (fun s : EuclideanSpace ℝ (Fin n) => s i) h
    simp [singletonPoint_apply, hij] at hc
  · rw [← supportFace_pair_eq_segment_singletons t mu i j hi hj hij]
    exact supportFace_isExtreme t mu {i, j}

/-- The carrier of an equal-moment singleton and a low/high pair is exactly
their segment. This includes the degenerate moment configurations omitted by
the pair-only diameter theorem. -/
theorem supportFace_triple_eq_segment_singleton_pair {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j k : Fin n)
    (hli : t i < mu) (hrj : mu < t j) (hk : t k = mu) :
    supportFace t mu {i, j, k} =
      segment ℝ (singletonPoint k) (pairPoint t mu i j) := by
  classical
  have hij : i ≠ j := by intro h; subst j; linarith
  have hik : i ≠ k := by intro h; subst k; linarith
  have hjk : j ≠ k := by intro h; subst k; linarith
  have hd : 0 < t j - t i := by linarith
  apply Set.Subset.antisymm
  · intro s hs
    have hzero : ∀ r, r ≠ i → r ≠ j → r ≠ k → s r = 0 := by
      intro r hri hrj' hrk
      exact hs.2 r (by simp [hri, hrj', hrk])
    have hsum := sum_eq_add_add_of_zero_off_triple (fun r => s r)
      i j k hij hik hjk hzero
    have hmass : s i + s j + s k = 1 := hsum.symm.trans hs.1.2.1
    have hmoment := sum_eq_add_add_of_zero_off_triple (fun r => t r * s r)
      i j k hij hik hjk (by
        intro r hri hrj' hrk
        change t r * s r = 0
        rw [hzero r hri hrj' hrk, mul_zero])
    have hmom : t i * s i + t j * s j + mu * s k = mu := by
      simpa only [hk] using hmoment.symm.trans hs.1.2.2
    have hnumi : (s i + s j) * (t j - mu) = s i * (t j - t i) := by
      linear_combination hmom - mu * hmass
    have hnumj : (s i + s j) * (mu - t i) = s j * (t j - t i) := by
      linear_combination mu * hmass - hmom
    have hab : s k + (s i + s j) = 1 := by linarith
    refine mem_segment_iff_div.mpr ⟨s k, s i + s j, hs.1.1 k,
      add_nonneg (hs.1.1 i) (hs.1.1 j), by rw [hab]; norm_num, ?_⟩
    ext r
    change s k / (s k + (s i + s j)) * singletonPoint k r +
      (s i + s j) / (s k + (s i + s j)) * pairPoint t mu i j r = s r
    rw [hab]
    simp only [div_one]
    by_cases hri : r = i
    · subst r
      rw [singletonPoint_apply, if_neg hik, mul_zero, zero_add, pairPoint_apply_left]
      rw [← mul_div_assoc]
      exact (div_eq_iff (ne_of_gt hd)).2 hnumi
    · by_cases hrj' : r = j
      · subst r
        rw [singletonPoint_apply, if_neg hjk, mul_zero, zero_add,
          pairPoint_apply_right t mu i j hij, ← mul_div_assoc]
        exact (div_eq_iff (ne_of_gt hd)).2 hnumj
      · by_cases hrk : r = k
        · subst r
          rw [singletonPoint_apply, if_pos rfl, mul_one,
            pairPoint_apply_other t mu i j k hik.symm hjk.symm, mul_zero, add_zero]
        · rw [singletonPoint_apply, if_neg hrk,
            pairPoint_apply_other t mu i j r hri hrj', hzero r hri hrj' hrk]
          ring
  · exact segment_subset_supportFace t mu {i, j, k} _ _
      (singletonPoint_mem_supportFace t mu k hk {i, j, k} (by simp))
      (pairPoint_mem_supportFace t mu i j hli hrj {i, j, k} (by simp) (by simp))

theorem singletonPoint_adj_pairPoint {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j k : Fin n)
    (hli : t i < mu) (hrj : mu < t j) (hk : t k = mu) :
    Adj (momentSlice t mu) (singletonPoint k) (pairPoint t mu i j) := by
  classical
  have hki : k ≠ i := by intro h; subst k; linarith
  have hkj : k ≠ j := by intro h; subst k; linarith
  refine ⟨?_, ?_⟩
  · intro h
    have hc := congrArg (fun s : EuclideanSpace ℝ (Fin n) => s k) h
    change singletonPoint k k = pairPoint t mu i j k at hc
    rw [singletonPoint_apply, if_pos rfl,
      pairPoint_apply_other t mu i j k hki hkj] at hc
    norm_num at hc
  · rw [← supportFace_triple_eq_segment_singleton_pair t mu i j k hli hrj hk]
    exact supportFace_isExtreme t mu {i, j, k}

/-- Every two extreme points of the entire normalized slice have a two-step
edge/stay route. Its intermediate vertex preserves all common zero
coordinates, so the route stays in every common support face. -/
theorem momentSlice_two_step_route {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (x y : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ extremePoints ℝ (momentSlice t mu))
    (hy : y ∈ extremePoints ℝ (momentSlice t mu)) :
    ∃ w ∈ extremePoints ℝ (momentSlice t mu),
      (x = w ∨ Adj (momentSlice t mu) x w) ∧
      (w = y ∨ Adj (momentSlice t mu) w y) ∧
      ∀ r, x r = 0 → y r = 0 → w r = 0 := by
  classical
  rcases extremePoints_classification t mu x hx with ⟨i, hi, rfl⟩ |
    ⟨i, j, hli, hrj, rfl⟩
  · rcases extremePoints_classification t mu y hy with ⟨k, hk, rfl⟩ |
      ⟨k, l, hlk, hrl, rfl⟩
    · refine ⟨singletonPoint i, hx, Or.inl rfl, ?_, fun _ h _ => h⟩
      by_cases hik : i = k
      · subst k
        exact Or.inl rfl
      · exact Or.inr (singletonPoint_adj_singletonPoint t mu i k hi hk hik)
    · exact ⟨singletonPoint i, hx, Or.inl rfl,
        Or.inr (singletonPoint_adj_pairPoint t mu k l i hlk hrl hi),
        fun _ h _ => h⟩
  · rcases extremePoints_classification t mu y hy with ⟨k, hk, rfl⟩ |
      ⟨k, l, hlk, hrl, rfl⟩
    · have hAdj := singletonPoint_adj_pairPoint t mu i j k hli hrj hk
      have hrev : Adj (momentSlice t mu) (pairPoint t mu i j) (singletonPoint k) := by
        refine ⟨hAdj.1.symm, ?_⟩
        simpa only [segment_symm] using hAdj.2
      exact ⟨singletonPoint k, hy, Or.inr hrev, Or.inl rfl, fun _ _ h => h⟩
    · have hroute := pairPoint_two_step_route t mu i k j l hli hlk hrj hrl
      refine ⟨pairPoint t mu i l, pairPoint_mem_extremePoints t mu i l hli hrl,
        hroute.1, hroute.2, ?_⟩
      intro r hxr hyr
      have hri : r ≠ i := by
        intro h
        subst r
        rw [pairPoint_apply_left] at hxr
        have hpos : 0 < (t j - mu) / (t j - t i) :=
          div_pos (sub_pos.mpr hrj) (sub_pos.mpr (hli.trans hrj))
        linarith
      have hkl : k ≠ l := by intro h; subst l; linarith
      have hrl' : r ≠ l := by
        intro h
        subst r
        rw [pairPoint_apply_right t mu k l hkl] at hyr
        have hpos : 0 < (mu - t k) / (t l - t k) :=
          div_pos (sub_pos.mpr hlk) (sub_pos.mpr (hlk.trans hrl))
        linarith
      exact pairPoint_apply_other t mu i l r hri hrl'

/-- The ordinary graph-diameter statement for the full slice. -/
theorem momentSlice_diamLE_two {n : ℕ} (t : Fin n → ℝ) (mu : ℝ) :
    DiamLE (momentSlice t mu) 2 := by
  intro x hx y hy
  obtain ⟨w, _hw, hxw, hwy, _hz⟩ := momentSlice_two_step_route t mu x y hx hy
  refine ⟨fun k => if k = 0 then x else if k = 1 then w else y,
    by simp, by norm_num, ?_⟩
  intro i hi
  have hcases : i = 0 ∨ i = 1 := by omega
  rcases hcases with rfl | rfl
  · simpa using hxw
  · simpa using hwy

/-- Two vertices lying in a given coordinate-support face have a two-step
route whose intermediate vertex also lies in that face. -/
theorem supportFace_two_step_route {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (S : Finset (Fin n))
    (x y : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ extremePoints ℝ (momentSlice t mu))
    (hy : y ∈ extremePoints ℝ (momentSlice t mu))
    (hxS : x ∈ supportFace t mu S) (hyS : y ∈ supportFace t mu S) :
    ∃ w ∈ extremePoints ℝ (momentSlice t mu),
      w ∈ supportFace t mu S ∧
      (x = w ∨ Adj (momentSlice t mu) x w) ∧
      (w = y ∨ Adj (momentSlice t mu) w y) := by
  obtain ⟨w, hw, hxw, hwy, hz⟩ := momentSlice_two_step_route t mu x y hx hy
  refine ⟨w, hw, ⟨(mem_extremePoints_iff_left.mp hw).1, ?_⟩, hxw, hwy⟩
  intro r hr
  exact hz r (hxS.2 r hr) (hyS.2 r hr)

#print axioms momentSlice_diamLE_two
#print axioms supportFace_two_step_route
#print axioms supportFace_pair_eq_segment_singletons
#print axioms singletonPoint_adj_singletonPoint
#print axioms supportFace_triple_eq_segment_singleton_pair
#print axioms singletonPoint_adj_pairPoint
#print axioms momentSlice_two_step_route

end HirschExcessTwo
