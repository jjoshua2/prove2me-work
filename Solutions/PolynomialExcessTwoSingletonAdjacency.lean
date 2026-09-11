import Solutions.PolynomialExcessTwoVertexClassification
import Solutions.PolynomialExcessTwoSharedAdjacency

/-!
# The missing edges incident to equal-moment singleton vertices

UNCOMPILED candidate continuation. No kernel or platform verdict is claimed.
Every proposed edge is proved via equality with a coordinate support face;
there is no inference from circuit status to graph adjacency.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace HirschExcessTwo

lemma singletonPoint_mem_supportFace {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i : Fin n) (hi : t i = mu)
    (S : Finset (Fin n)) (hiS : i ∈ S) :
    singletonPoint i ∈ supportFace t mu S := by
  classical
  refine ⟨singletonPoint_mem t mu i hi, ?_⟩
  intro k hk
  have hki : k ≠ i := by intro h; subst k; exact hk hiS
  simp [singletonPoint_apply, hki]

/-- The support face on two distinct equal-moment coordinates is their segment. -/
theorem supportFace_pair_eq_segment_singletons {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j : Fin n)
    (hi : t i = mu) (hj : t j = mu) (hij : i ≠ j) :
    supportFace t mu {i, j} = segment ℝ (singletonPoint i) (singletonPoint j) := by
  classical
  apply Set.Subset.antisymm
  · intro s hs
    have hz : ∀ k, k ≠ i → k ≠ j → s k = 0 := by
      intro k hki hkj
      exact hs.2 k (by simp [hki, hkj])
    have hmass : s i + s j = 1 :=
      (sum_eq_add_of_zero_off_pair (fun k => s k) i j hij hz).symm.trans hs.1.2.1
    apply mem_segment_iff_div.mpr
    refine ⟨s i, s j, hs.1.1 i, hs.1.1 j, by linarith, ?_⟩
    simp only [hmass, div_one]
    ext k
    change s i * singletonPoint i k + s j * singletonPoint j k = s k
    by_cases hki : k = i
    · subst k
      simp [singletonPoint_apply, hij]
    · by_cases hkj : k = j
      · subst k
        simp [singletonPoint_apply, hij.symm]
      · simp [singletonPoint_apply, hki, hkj, hz k hki hkj]
  · exact segment_subset_supportFace t mu {i, j}
      (singletonPoint i) (singletonPoint j)
      (singletonPoint_mem_supportFace t mu i hi {i, j} (by simp))
      (singletonPoint_mem_supportFace t mu j hj {i, j} (by simp))

/-- Distinct equal-moment singleton vertices are joined by an actual edge. -/
theorem singletonPoint_adj_singletonPoint {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j : Fin n)
    (hi : t i = mu) (hj : t j = mu) (hij : i ≠ j) :
    Adj (momentSlice t mu) (singletonPoint i) (singletonPoint j) := by
  classical
  have hne : singletonPoint i ≠ singletonPoint j := by
    intro h
    have hc := congrArg (fun s : EuclideanSpace ℝ (Fin n) => s i) h
    have hbad : (1 : ℝ) = 0 := by simpa [singletonPoint_apply, hij] using hc
    norm_num at hbad
  refine ⟨hne, ?_⟩
  rw [← supportFace_pair_eq_segment_singletons t mu i j hi hj hij]
  exact supportFace_isExtreme t mu {i, j}

/-- The carrier on one equal-moment coordinate and one low/high pair is exactly
the segment from the singleton to the pair vertex. The formula also handles
zero mass at either endpoint without division by that mass. -/
theorem supportFace_triple_eq_segment_singleton_pair {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (k i j : Fin n)
    (hk : t k = mu) (hli : t i < mu) (hrj : mu < t j) :
    supportFace t mu {k, i, j} =
      segment ℝ (singletonPoint k) (pairPoint t mu i j) := by
  classical
  have hki : k ≠ i := by intro h; subst k; linarith
  have hkj : k ≠ j := by intro h; subst k; linarith
  have hij : i ≠ j := by intro h; subst i; linarith
  have hden : 0 < t j - t i := sub_pos.mpr (hli.trans hrj)
  apply Set.Subset.antisymm
  · intro s hs
    have hz : ∀ r, r ≠ k → r ≠ i → r ≠ j → s r = 0 := by
      intro r hrk hri hrj'
      exact hs.2 r (by simp [hrk, hri, hrj'])
    have hmass : s k + s i + s j = 1 :=
      (sum_eq_add_add_of_zero_off_triple (fun r => s r) k i j
        hki hkj hij hz).symm.trans hs.1.2.1
    have hmom : mu * s k + t i * s i + t j * s j = mu := by
      have h := (sum_eq_add_add_of_zero_off_triple (fun r => t r * s r)
        k i j hki hkj hij (by
          intro r hrk hri hrj'
          rw [hz r hrk hri hrj', mul_zero])).symm.trans hs.1.2.2
      simpa only [hk] using h
    have hsi : s i * (t j - t i) = (s i + s j) * (t j - mu) := by
      linear_combination mu * hmass - hmom
    have hsj : s j * (t j - t i) = (s i + s j) * (mu - t i) := by
      linear_combination hmom - mu * hmass
    have hsum : s k + (s i + s j) = 1 := by linarith
    apply mem_segment_iff_div.mpr
    refine ⟨s k, s i + s j, hs.1.1 k, add_nonneg (hs.1.1 i) (hs.1.1 j),
      by linarith, ?_⟩
    simp only [hsum, div_one]
    ext r
    change s k * singletonPoint k r + (s i + s j) * pairPoint t mu i j r = s r
    by_cases hrk : r = k
    · subst r
      rw [pairPoint_apply_other t mu i j k hki hkj]
      simp
    · by_cases hri : r = i
      · subst r
        simp only [singletonPoint_apply, if_neg hrk, mul_zero, zero_add,
          pairPoint_apply_left]
        calc
          (s i + s j) * ((t j - mu) / (t j - t i)) =
              ((s i + s j) * (t j - mu)) / (t j - t i) := by ring
          _ = s i := (div_eq_iff (ne_of_gt hden)).mpr hsi.symm
      · by_cases hrj' : r = j
        · subst r
          simp only [singletonPoint_apply, if_neg hrk, mul_zero, zero_add,
            pairPoint_apply_right t mu i j hij]
          calc
            (s i + s j) * ((mu - t i) / (t j - t i)) =
                ((s i + s j) * (mu - t i)) / (t j - t i) := by ring
            _ = s j := (div_eq_iff (ne_of_gt hden)).mpr hsj.symm
        · rw [pairPoint_apply_other t mu i j r hri hrj', hz r hrk hri hrj']
          simp [singletonPoint_apply, hrk]
  · exact segment_subset_supportFace t mu {k, i, j}
      (singletonPoint k) (pairPoint t mu i j)
      (singletonPoint_mem_supportFace t mu k hk {k, i, j} (by simp))
      (pairPoint_mem_supportFace t mu i j hli hrj {k, i, j} (by simp) (by simp))

/-- An equal-moment singleton is adjacent to every low/high pair vertex. -/
theorem singletonPoint_adj_pairPoint {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (k i j : Fin n)
    (hk : t k = mu) (hli : t i < mu) (hrj : mu < t j) :
    Adj (momentSlice t mu) (singletonPoint k) (pairPoint t mu i j) := by
  classical
  have hki : k ≠ i := by intro h; subst k; linarith
  have hkj : k ≠ j := by intro h; subst k; linarith
  have hne : singletonPoint k ≠ pairPoint t mu i j := by
    intro h
    have hc := congrArg (fun s : EuclideanSpace ℝ (Fin n) => s k) h
    change singletonPoint k k = pairPoint t mu i j k at hc
    rw [pairPoint_apply_other t mu i j k hki hkj] at hc
    have hbad : (1 : ℝ) = 0 := by simpa using hc
    norm_num at hbad
  refine ⟨hne, ?_⟩
  rw [← supportFace_triple_eq_segment_singleton_pair t mu k i j hk hli hrj]
  exact supportFace_isExtreme t mu {k, i, j}

#print axioms supportFace_pair_eq_segment_singletons
#print axioms singletonPoint_adj_singletonPoint
#print axioms supportFace_triple_eq_segment_singleton_pair
#print axioms singletonPoint_adj_pairPoint

end HirschExcessTwo
