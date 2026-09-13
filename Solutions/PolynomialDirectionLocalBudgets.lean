import Mathlib

/-!
# Direction-local joint budgets

For a fixed parent edge, all nonzero candidate edge contributions lie in ONE
candidate direction group. These finite identities prove that local group
budgets and the global edge budget are equivalent, even for overlapping groups.
The geometric derivation of that cover uses supporting faces and the classical
Shephard summand criterion; it is written out in the companion note, not
introduced here as an unexplained polytope axiom.

The last lemma gives a weighted distance lower bound after each step's changes
are charged to one direction group. NEW UNCOMPILED candidates. No platform or
end-to-end polytope formalization verdict is asserted.
-/
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace HirschDirectionLocal
variable {ι ε : Type*} [Fintype ι] [DecidableEq ι]

lemma sum_eq_group (I : Finset ι) (f : ι → ℝ)
    (hz : ∀ i, i ∉ I → f i = 0) :
    (∑ i, f i) = ∑ i in I, f i := by
  symm
  apply Finset.sum_subset (Finset.subset_univ I)
  intro i _ hi
  exact hz i hi

/-- Each group is tested on every parent edge, but one group contains all
nonzero contributions on any given edge. No disjointness of groups is needed. -/
theorem global_budget_iff_group_budgets
    (groups : Finset (Finset ι)) (length : ε → ι → ℝ)
    (capacity : ε → ℝ) (scale : ι → ℝ)
    (hs : ∀ i, 0 ≤ scale i) (hl : ∀ e i, 0 ≤ length e i)
    (hcover : ∀ e, ∃ I ∈ groups, ∀ i, i ∉ I → length e i = 0) :
    (∀ e, (∑ i, scale i * length e i) ≤ capacity e) ↔
      (∀ I ∈ groups, ∀ e, (∑ i in I, scale i * length e i) ≤ capacity e) := by
  constructor
  · intro h I _ e
    have hsub : (∑ i in I, scale i * length e i) ≤
        ∑ i, scale i * length e i := by
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

/-- A failed global edge capacity is witnessed by one local direction group,
not by an unbounded collection of unrelated candidate directions. -/
theorem violated_budget_has_group_witness
    (groups : Finset (Finset ι)) (length : ι → ℝ) (scale : ι → ℝ)
    (capacity : ℝ)
    (hcover : ∃ I ∈ groups, ∀ i, i ∉ I → length i = 0)
    (hbad : capacity < ∑ i, scale i * length i) :
    ∃ I ∈ groups, capacity < ∑ i in I, scale i * length i := by
  obtain ⟨I,hI,hzero⟩ := hcover
  refine ⟨I,hI,?_⟩
  have he := sum_eq_group I (fun i => scale i * length i)
    (fun i hi => by rw [hzero i hi, mul_zero])
  rwa [he] at hbad

/-- Each endpoint-discrepant factor needs at least one transition. A nonnegative
weight packing that charges every actual edge by at most one is a lower bound
for EVERY route, not only the route returned by the constructor. -/
theorem weighted_transition_lower_bound
    (L : ℕ) (weight demand : ι → ℝ) (change : ι → Fin L → ℝ)
    (hw : ∀ i, 0 ≤ weight i)
    (hd : ∀ i, demand i ≤ ∑ j, change i j)
    (hstep : ∀ j, (∑ i, weight i * change i j) ≤ 1) :
    (∑ i, weight i * demand i) ≤ (L : ℝ) := by
  calc
    (∑ i, weight i * demand i) ≤ ∑ i, weight i * ∑ j, change i j :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hd i) (hw i))
    _ = ∑ j, ∑ i, weight i * change i j := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ _j : Fin L, (1 : ℝ) := Finset.sum_le_sum (fun j _ => hstep j)
    _ = (L : ℝ) := by simp

#print axioms sum_eq_group
#print axioms global_budget_iff_group_budgets
#print axioms violated_budget_has_group_witness
#print axioms weighted_transition_lower_bound
end HirschDirectionLocal
