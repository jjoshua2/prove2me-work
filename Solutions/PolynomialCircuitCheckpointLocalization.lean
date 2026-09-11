import Mathlib
import Solutions.PolynomialRowRankDeletion

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option maxHeartbeats 4000000

noncomputable section

/-!
Candidate source, not yet compiled in the pinned Lean environment.

This extends vertex-to-vertex circuit localization to nonvertex checkpoints.
The endpoint terms are tight-row nullities `commonFaceDim a b x x` and
`commonFaceDim a b y y`. For feasible points these are their minimal-face
coordinate dimensions. The general inequality also includes the defect of
ALL direction-neutral rows, not merely the source-active neutral rows.
-/
namespace HirschCircuitLocalization

open HirschPolynomialAccess

variable {d n : ℕ}

/-- The ambient row-neutral rank deficit. This is different from
`HirschPolynomialAccess.activeNeutralDefect`, which only uses source-active
rows. No feasibility assumption is built into this definition. -/
noncomputable def directionNeutralDefect
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d)) : ℕ :=
  (d - 1) - Module.finrank ℝ
    (rowEvalMap a (circuitNeutralRows a g)).range

/-- Nullity form of the checked row-deletion inequality. -/
theorem rowEval_nullity_le_supernullity_add_deleted
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (S T : Finset (Fin n)) (hST : S ⊆ T) :
    Module.finrank ℝ (rowEvalMap a S).ker ≤
      Module.finrank ℝ (rowEvalMap a T).ker + (T \ S).card := by
  classical
  have htop (U : Finset (Fin n)) :
      (((rowEvalMap a U).domRestrict
        (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin d)))).range) =
        (rowEvalMap a U).range := by
    ext z
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨(x : EuclideanSpace ℝ (Fin d)), hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨⟨x, by simp⟩, hx⟩
  have hr := restricted_rowEval_rank_le_subrank_add_deleted a
    (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin d))) S T hST
  rw [htop T, htop S] at hr
  have hS := (rowEvalMap a S).finrank_range_add_finrank_ker
  have hT := (rowEvalMap a T).finrank_range_add_finrank_ker
  have harith : ∀ rs ks rt kt q : ℕ,
      rs + ks = rt + kt → rt ≤ rs + q → ks ≤ kt + q := by
    intros
    omega
  exact harith _ _ _ _ _ (hS.trans hT.symm) hr

/-- Losing source-tight rows can enlarge the common carrier by at most the
number lost, in addition to the source's original tight-row nullity. -/
theorem commonFaceDim_le_sourceOnlyRows_card_add_sourceNullity
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    commonFaceDim a b x y ≤
      (sourceOnlyRows a b x y).card + commonFaceDim a b x x := by
  classical
  have hsub : commonSourceRows a b x y ⊆ commonSourceRows a b x x := by
    intro i hi
    have h := (Finset.mem_filter.1 hi).2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ i, h.1, h.2.1, h.2.1⟩
  have hdiff : commonSourceRows a b x x \ commonSourceRows a b x y =
      sourceOnlyRows a b x y := by
    ext i
    simp only [commonSourceRows, sourceOnlyRows, Finset.mem_sdiff,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hai, hix, _⟩, hn⟩
      exact ⟨hai, hix, fun hiy => hn ⟨hai, hix, hiy⟩⟩
    · rintro ⟨hai, hix, hiy⟩
      exact ⟨⟨hai, hix, hix⟩, fun h => hiy h.2.2⟩
  have h := rowEval_nullity_le_supernullity_add_deleted a
    (commonSourceRows a b x y) (commonSourceRows a b x x) hsub
  change commonFaceDim a b x y ≤ commonFaceDim a b x x +
    (commonSourceRows a b x x \ commonSourceRows a b x y).card at h
  rw [hdiff] at h
  simpa only [Nat.add_comm] using h

/-- Target version of the same nullity estimate. -/
theorem commonFaceDim_le_targetOnlyRows_card_add_targetNullity
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    commonFaceDim a b x y ≤
      (targetOnlyRows a b x y).card + commonFaceDim a b y y := by
  classical
  have hC : commonSourceRows a b y x = commonSourceRows a b x y := by
    ext i
    simp [commonSourceRows, and_comm, and_left_comm, and_assoc]
  have hdim : commonFaceDim a b y x = commonFaceDim a b x y := by
    unfold commonFaceDim commonDirection
    rw [hC]
  have hS : sourceOnlyRows a b y x = targetOnlyRows a b x y := by
    ext i
    simp [sourceOnlyRows, targetOnlyRows, and_comm, and_left_comm, and_assoc]
  have h := commonFaceDim_le_sourceOnlyRows_card_add_sourceNullity a b y x
  rw [hdim, hS] at h
  exact h

/-- General checkpoint localization. Neither checkpoint needs to be a vertex,
and the direction need not be a circuit. The two endpoint nullities and the
all-neutral rank defect are explicit correction terms. -/
theorem commonFaceDim_checkpoint_localization_with_directionDefect
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    2 * commonFaceDim a b x y + d ≤
      n + commonFaceDim a b x x + commonFaceDim a b y y +
        directionNeutralDefect a (y - x) + 1 := by
  classical
  let S := sourceOnlyRows a b x y
  let T := targetOnlyRows a b x y
  let Z := circuitNeutralRows a (y - x)
  have hS : commonFaceDim a b x y ≤ S.card + commonFaceDim a b x x :=
    commonFaceDim_le_sourceOnlyRows_card_add_sourceNullity a b x y
  have hT : commonFaceDim a b x y ≤ T.card + commonFaceDim a b y y :=
    commonFaceDim_le_targetOnlyRows_card_add_targetNullity a b x y
  have hZrank : Module.finrank ℝ (rowEvalMap a Z).range ≤ Z.card := by
    calc
      _ ≤ Module.finrank ℝ (Z → ℝ) := Submodule.finrank_le _
      _ = Z.card := by simp [Fintype.card_coe]
  have hZ : d ≤ Z.card + directionNeutralDefect a (y - x) + 1 := by
    have harith : ∀ d r z : ℕ, r ≤ z → d ≤ z + ((d - 1) - r) + 1 := by
      intros
      omega
    exact harith d _ _ hZrank
  have hST : Disjoint S T := by
    refine Finset.disjoint_left.2 ?_
    intro i hiS hiT
    have hs := (Finset.mem_filter.1 hiS).2
    have ht := (Finset.mem_filter.1 hiT).2
    exact ht.2.1 hs.2.1
  have hSZ : Disjoint S Z := by
    refine Finset.disjoint_left.2 ?_
    intro i hiS hiZ
    have hs := (Finset.mem_filter.1 hiS).2
    have hz := (Finset.mem_filter.1 hiZ).2
    have hz0 : ⟪a i, y - x⟫ = 0 := hz.2
    rw [inner_sub_right] at hz0
    have hyEq : ⟪a i, y⟫ = b i := by linarith [hs.2.1]
    exact hs.2.2 hyEq
  have hTZ : Disjoint T Z := by
    refine Finset.disjoint_left.2 ?_
    intro i hiT hiZ
    have ht := (Finset.mem_filter.1 hiT).2
    have hz := (Finset.mem_filter.1 hiZ).2
    have hz0 : ⟪a i, y - x⟫ = 0 := hz.2
    rw [inner_sub_right] at hz0
    have hxEq : ⟪a i, x⟫ = b i := by linarith [ht.2.2]
    exact ht.2.1 hxEq
  have hSTZ : Disjoint (S ∪ T) Z := Finset.disjoint_union_left.2 ⟨hSZ, hTZ⟩
  have hcount : (S ∪ T ∪ Z).card ≤ n := by
    calc
      _ ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (by simp)
      _ = n := by simp
  rw [Finset.card_union_of_disjoint hSTZ,
    Finset.card_union_of_disjoint hST] at hcount
  have harith : ∀ h d n s t z p q δ : ℕ,
      h ≤ s + p → h ≤ t + q → d ≤ z + δ + 1 → s + t + z ≤ n →
      2 * h + d ≤ n + p + q + δ + 1 := by
    intros
    omega
  exact harith _ _ _ _ _ _ _ _ _ hS hT hZ hcount

/-- A row circuit has zero all-neutral defect when the presentation has an
extreme point. The reference vertex need not be either checkpoint. -/
theorem directionNeutralDefect_eq_zero_of_rowCircuit
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (z g : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ extremePoints ℝ (Hpoly a b))
    (hg : IsRowCircuit a g) : directionNeutralDefect a g = 0 := by
  unfold directionNeutralDefect
  rw [rowCircuit_neutral_rank_eq_dim_sub_one a b z g hz hg, Nat.sub_self]

/-- Nonvertex version of the sharp circuit localization theorem. -/
theorem rowCircuit_commonFaceDim_checkpoint_localization
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (z x y : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ extremePoints ℝ (Hpoly a b))
    (hg : IsRowCircuit a (y - x)) :
    2 * commonFaceDim a b x y + d ≤
      n + commonFaceDim a b x x + commonFaceDim a b y y + 1 := by
  have h := commonFaceDim_checkpoint_localization_with_directionDefect a b x y
  rw [directionNeutralDefect_eq_zero_of_rowCircuit a b z (y - x) hz hg] at h
  simpa only [Nat.add_zero] using h

#print axioms rowEval_nullity_le_supernullity_add_deleted
#print axioms commonFaceDim_le_sourceOnlyRows_card_add_sourceNullity
#print axioms commonFaceDim_le_targetOnlyRows_card_add_targetNullity
#print axioms commonFaceDim_checkpoint_localization_with_directionDefect
#print axioms directionNeutralDefect_eq_zero_of_rowCircuit
#print axioms rowCircuit_commonFaceDim_checkpoint_localization

end HirschCircuitLocalization
