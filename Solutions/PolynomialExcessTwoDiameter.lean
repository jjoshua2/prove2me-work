import Solutions.PolynomialExcessTwoSingletonAdjacency

/-!
# Full, support-preserving diameter two for the normalized moment slice

UNCOMPILED candidate. These declarations are not yet kernel-verified or
Prove2Me-published. No claim about a general H-polytope is made without an
additional affine slack-model equivalence.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace HirschExcessTwo

private lemma reverse_edge {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {u v : E} (h : Adj P u v) : Adj P v u := by
  refine ⟨h.1.symm, ?_⟩
  simpa only [segment_symm] using h.2

/-- Complete two-step routing. The intermediate vertex preserves every
coordinate which is zero at both endpoints, so it remains in their common
coordinate support face. -/
theorem momentSlice_two_step_route_preserving_zeros {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ)
    (x y : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ extremePoints ℝ (momentSlice t mu))
    (hy : y ∈ extremePoints ℝ (momentSlice t mu)) :
    ∃ z : EuclideanSpace ℝ (Fin n),
      z ∈ extremePoints ℝ (momentSlice t mu) ∧
      (x = z ∨ Adj (momentSlice t mu) x z) ∧
      (z = y ∨ Adj (momentSlice t mu) z y) ∧
      (∀ r, x r = 0 → y r = 0 → z r = 0) := by
  classical
  rcases (momentSlice_extremePoints_iff t mu x).mp hx with
    ⟨k, hk, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
  · rcases (momentSlice_extremePoints_iff t mu y).mp hy with
      ⟨l, hl, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
    · refine ⟨singletonPoint k, hx, Or.inl rfl, ?_, ?_⟩
      · by_cases hkl : k = l
        · subst l
          exact Or.inl rfl
        · exact Or.inr (singletonPoint_adj_singletonPoint t mu k l hk hl hkl)
      · intro r hr _
        exact hr
    · refine ⟨singletonPoint k, hx, Or.inl rfl,
        Or.inr (singletonPoint_adj_pairPoint t mu k i j hk hi hj), ?_⟩
      intro r hr _
      exact hr
  · rcases (momentSlice_extremePoints_iff t mu y).mp hy with
      ⟨k, hk, rfl⟩ | ⟨k, l, hk, hl, rfl⟩
    · refine ⟨singletonPoint k, hy,
        Or.inr (reverse_edge (singletonPoint_adj_pairPoint t mu k i j hk hi hj)),
        Or.inl rfl, ?_⟩
      intro r _ hr
      exact hr
    · obtain ⟨hfirst, hsecond⟩ := pairPoint_two_step_route t mu i k j l hi hk hj hl
      refine ⟨pairPoint t mu i l, pairPoint_mem_extremePoints t mu i l hi hl,
        hfirst, hsecond, ?_⟩
      intro r hx0 hy0
      have hir : r ≠ i := by
        intro h
        subst r
        have hp : 0 < pairPoint t mu i j i := by
          rw [pairPoint_apply_left]
          exact div_pos (sub_pos.mpr hj) (sub_pos.mpr (hi.trans hj))
        linarith
      have hlr : r ≠ l := by
        intro h
        subst r
        have hkl : k ≠ l := by intro h; subst l; linarith
        have hp : 0 < pairPoint t mu k l l := by
          rw [pairPoint_apply_right t mu k l hkl]
          exact div_pos (sub_pos.mpr hk) (sub_pos.mpr (hk.trans hl))
        linarith
      exact pairPoint_apply_other t mu i l r hir hlr

/-- The full theorem also applies inside each coordinate support face, with
edges of that face rather than merely ambient edges. -/
theorem supportFace_two_step_route {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (S : Finset (Fin n))
    (x y : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ extremePoints ℝ (supportFace t mu S))
    (hy : y ∈ extremePoints ℝ (supportFace t mu S)) :
    ∃ z : EuclideanSpace ℝ (Fin n),
      z ∈ extremePoints ℝ (supportFace t mu S) ∧
      (x = z ∨ Adj (supportFace t mu S) x z) ∧
      (z = y ∨ Adj (supportFace t mu S) z y) := by
  have hface := supportFace_isExtreme t mu S
  have hxP := hface.extremePoints_subset_extremePoints hx
  have hyP := hface.extremePoints_subset_extremePoints hy
  obtain ⟨z, hzP, hfirst, hsecond, hzeros⟩ :=
    momentSlice_two_step_route_preserving_zeros t mu x y hxP hyP
  have hzS : z ∈ supportFace t mu S := by
    refine ⟨hzP.1, ?_⟩
    intro r hr
    exact hzeros r (hx.1.2 r hr) (hy.1.2 r hr)
  have hz : z ∈ extremePoints ℝ (supportFace t mu S) :=
    inter_extremePoints_subset_extremePoints_of_subset
      (supportFace_subset t mu S) ⟨hzS, hzP⟩
  have restrict_edge : ∀ p q : EuclideanSpace ℝ (Fin n),
      p ∈ supportFace t mu S → q ∈ supportFace t mu S →
      Adj (momentSlice t mu) p q → Adj (supportFace t mu S) p q := by
    intro p q hp hq he
    exact ⟨he.1, he.2.mono (supportFace_subset t mu S)
      (segment_subset_supportFace t mu S p q hp hq)⟩
  refine ⟨z, hz, ?_, ?_⟩
  · rcases hfirst with heq | he
    · exact Or.inl heq
    · exact Or.inr (restrict_edge x z hx.1 hzS he)
  · rcases hsecond with heq | he
    · exact Or.inl heq
    · exact Or.inr (restrict_edge z y hzS hy.1 he)

private theorem diamLE_two_of_midpoints
    {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E)
    (h : ∀ x ∈ extremePoints ℝ P, ∀ y ∈ extremePoints ℝ P,
      ∃ z : E, (x = z ∨ Adj P x z) ∧ (z = y ∨ Adj P z y)) : DiamLE P 2 := by
  intro x hx y hy
  obtain ⟨z, hxz, hzy⟩ := h x hx y hy
  refine ⟨fun k => if k = 0 then x else if k = 1 then z else y,
    by simp, by norm_num, ?_⟩
  intro k hk
  have hk01 : k = 0 ∨ k = 1 := by omega
  rcases hk01 with rfl | rfl
  · simpa using hxz
  · simpa using hzy

/-- Full normalized moment-slice graph diameter is at most two.
There are no genericity, dimension, nonemptiness, or strict-feasibility assumptions. -/
theorem momentSlice_diamLE_two {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) : DiamLE (momentSlice t mu) 2 := by
  apply diamLE_two_of_midpoints
  intro x hx y hy
  obtain ⟨z, _hz, hfirst, hsecond, _hzeros⟩ :=
    momentSlice_two_step_route_preserving_zeros t mu x y hx hy
  exact ⟨z, hfirst, hsecond⟩

/-- Every coordinate support face has intrinsic graph diameter at most two. -/
theorem supportFace_diamLE_two {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (S : Finset (Fin n)) :
    DiamLE (supportFace t mu S) 2 := by
  apply diamLE_two_of_midpoints
  intro x hx y hy
  obtain ⟨z, _hz, hfirst, hsecond⟩ := supportFace_two_step_route t mu S x y hx hy
  exact ⟨z, hfirst, hsecond⟩

#print axioms momentSlice_two_step_route_preserving_zeros
#print axioms supportFace_two_step_route
#print axioms momentSlice_diamLE_two
#print axioms supportFace_diamLE_two

end HirschExcessTwo
