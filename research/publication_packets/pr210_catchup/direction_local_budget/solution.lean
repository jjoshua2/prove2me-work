import Mathlib
open scoped BigOperators
set_option autoImplicit false
noncomputable section

private lemma sum_eq_group {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : Finset ι) (f : ι → ℝ) (hz : ∀ i, i ∉ I → f i = 0) :
    (∑ i, f i) = ∑ i in I, f i := by
  symm
  apply Finset.sum_subset (Finset.subset_univ I)
  intro i _ hi
  exact hz i hi

theorem solution
    {ι ε : Type*} [Fintype ι] [DecidableEq ι]
    (groups : Finset (Finset ι)) (length : ε → ι → ℝ)
    (capacity : ε → ℝ) (scale : ι → ℝ)
    (hs : ∀ i, 0 ≤ scale i) (hl : ∀ e i, 0 ≤ length e i)
    (hcover : ∀ e, ∃ I ∈ groups, ∀ i, i ∉ I → length e i = 0) :
    (∀ e, (∑ i, scale i * length e i) ≤ capacity e) ↔
      (∀ I ∈ groups, ∀ e, (∑ i in I, scale i * length e i) ≤ capacity e) := by
  constructor
  · intro h I _ e
    have hsub : (∑ i in I, scale i * length e i) ≤ ∑ i, scale i * length e i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
      intro i _ _
      exact mul_nonneg (hs i) (hl e i)
    exact hsub.trans (h e)
  · intro h e
    obtain ⟨I,hI,hzero⟩ := hcover e
    have he := sum_eq_group I (fun i => scale i * length e i)
      (fun i hi => by rw [hzero i hi, mul_zero])
    rw [he]
    exact h I hI e

#print axioms solution
