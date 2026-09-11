import Mathlib
import Solutions.PolynomialCircuitBoundedNeutralRank
import Solutions.PolynomialCircuitCheckpointMinSubpresentationDefect

/-!
# Reference-free minimum-subpresentation defect accounting

The preceding nonvertex checkpoint theorem still carried an auxiliary parent
vertex solely to recover the ambient row-circuit neutral rank.  Boundedness and
source feasibility already give that rank identity directly, so the auxiliary
vertex can be removed entirely.
-/

open scoped BigOperators RealInnerProductSpace
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- Subtraction-free selected-effective-row defect budget for an arbitrary
feasible row-circuit checkpoint in a bounded parent.  No parent vertex or
checkpoint extremality is needed. -/
theorem rowCircuit_selectedEffectiveRows_defect_budget_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hx : x ∈ Hpoly a b)
    (hcirc : IsRowCircuit a (y - x))
    (F : Finset (Fin n))
    (hF : F ⊆ effectiveRowsOnSubspace a (commonDirection a b x y)) :
    F.card +
        ((commonFaceDim a b x y - 1) -
          Module.finrank ℝ
            (((rowEvalMap a (F ∩ circuitNeutralRows a (y - x))).domRestrict
              (commonDirection a b x y)).range)) +
        d ≤
      n + commonFaceDim a b x y := by
  classical
  let W := commonDirection a b x y
  let E := effectiveRowsOnSubspace a W
  let Z := circuitNeutralRows a (y - x)
  let T := Z ∩ E
  let S := F ∩ Z
  have hfull :
      Module.finrank ℝ (((rowEvalMap a T).domRestrict W).range) =
        Module.finrank ℝ W - 1 := by
    calc
      Module.finrank ℝ (((rowEvalMap a T).domRestrict W).range) =
          Module.finrank ℝ (((rowEvalMap a Z).domRestrict W).range) := by
            simpa [T, Z, E] using restricted_rowEval_effective_rank_eq a W Z
      _ = Module.finrank ℝ W - 1 := by
            simpa [Z, W, commonFaceDim] using
              rowCircuit_neutral_rank_on_commonDirection_eq_commonFaceDim_sub_one_of_bounded
                a b hbd x y hx hcirc
  have hST : S ⊆ T := by
    intro i hiS
    have hi := Finset.mem_inter.1 hiS
    exact Finset.mem_inter.2 ⟨hi.2, hF hi.1⟩
  have hdef :
      (Module.finrank ℝ W - 1) -
          Module.finrank ℝ (((rowEvalMap a S).domRestrict W).range) ≤
        (T \ S).card :=
    restricted_rowEval_defect_le_deleted a W S T hST hfull
  have hdelSub : T \ S ⊆ E \ F := by
    intro i hi
    have hiTS := Finset.mem_sdiff.1 hi
    have hiT := Finset.mem_inter.1 hiTS.1
    apply Finset.mem_sdiff.2
    refine ⟨hiT.2, ?_⟩
    intro hiFmem
    apply hiTS.2
    exact Finset.mem_inter.2 ⟨hiFmem, hiT.1⟩
  have hdefE :
      (Module.finrank ℝ W - 1) -
          Module.finrank ℝ (((rowEvalMap a S).domRestrict W).range) ≤
        (E \ F).card :=
    hdef.trans (Finset.card_le_card hdelSub)
  have hbudget : E.card + d ≤ n + Module.finrank ℝ W := by
    simpa [E, W, commonFaceDim] using
      commonDirection_effectiveRows_card_add_dim_le_rows_add_faceDim a b x y
  have hF' : F ⊆ E := by simpa [E, W] using hF
  have hcard : (E \ F).card + F.card = E.card :=
    Finset.card_sdiff_add_card_eq_card hF'
  have hmain :
      F.card +
          ((Module.finrank ℝ W - 1) -
            Module.finrank ℝ (((rowEvalMap a S).domRestrict W).range)) + d ≤
        n + Module.finrank ℝ W := by
    omega
  simpa [S, Z, W, commonFaceDim] using hmain

/-- Selected-effective-row excess/neutral-defect accounting for an arbitrary
feasible row-circuit checkpoint in a bounded parent. -/
theorem rowCircuit_selectedEffectiveRows_excess_defect_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hx : x ∈ Hpoly a b)
    (hcirc : IsRowCircuit a (y - x))
    (F : Finset (Fin n))
    (hF : F ⊆ effectiveRowsOnSubspace a (commonDirection a b x y))
    (hface : commonFaceDim a b x y ≤ F.card) :
    (F.card - commonFaceDim a b x y) +
        ((commonFaceDim a b x y - 1) -
          Module.finrank ℝ
            (((rowEvalMap a (F ∩ circuitNeutralRows a (y - x))).domRestrict
              (commonDirection a b x y)).range)) ≤
      n - d := by
  have h := rowCircuit_selectedEffectiveRows_defect_budget_of_bounded
    a b x y hbd hx hcirc F hF
  have hdn : d ≤ n := rows_ge_dimension_of_bounded a b hbd x hx
  omega

/-- Final reference-free checkpoint theorem.  For every feasible source `x` in
a bounded parent and every ambient row-circuit displacement `y-x`, minimum
presentation excess plus selected neutral-rank defect is bounded by the ambient
row excess `n-d`. -/
theorem rowCircuit_commonFace_minSubpresentation_excess_defect_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hx : x ∈ Hpoly a b)
    (hcirc : IsRowCircuit a (y - x)) :
    let M := commonFaceMinSubpresentationCount a b x y
    ∃ e : Fin M ↪ Fin n,
      Hpoly
          (fun j => HirschCommonFace.commonFaceA a b x y (e j))
          (fun j => HirschCommonFace.commonFaceB a b x y (e j)) =
        Hpoly
          (HirschCommonFace.commonFaceA a b x y)
          (HirschCommonFace.commonFaceB a b x y) ∧
      let F : Finset (Fin n) :=
        (Finset.univ.map e) ∩ HirschCommonFace.commonFaceEffectiveRows a b x y
      F.card = M ∧
      (M - HirschCommonFace.commonFaceDim a b x y) +
          ((HirschCommonFace.commonFaceDim a b x y - 1) -
            Module.finrank ℝ
              (((HirschCommonFace.rowEvalMap a
                (F ∩ Finset.univ.filter (fun i =>
                  a i ≠ 0 ∧ ⟪a i, y - x⟫ = 0))).domRestrict
                (HirschCommonFace.commonDirection a b x y)).range)) ≤
        n - d := by
  classical
  let M := commonFaceMinSubpresentationCount a b x y
  obtain ⟨e, he, hFeq⟩ :=
    commonFace_minSubpresentation_effective_witness_of_feasible a b x y hx
  refine ⟨e, he, ?_⟩
  let F : Finset (Fin n) :=
    (Finset.univ.map e) ∩ HirschCommonFace.commonFaceEffectiveRows a b x y
  have hFM : F.card = commonFaceMinSubpresentationCount a b x y := by
    simpa [F] using hFeq
  have hFpub : F ⊆ HirschCommonFace.commonFaceEffectiveRows a b x y :=
    Finset.inter_subset_right
  have hFint : F ⊆ effectiveRowsOnSubspace a (commonDirection a b x y) := by
    rw [effectiveRowsOn_commonDirection_eq_publicCommonFaceEffectiveRows]
    exact hFpub
  have hdimM := commonFaceDim_le_minSubpresentation_of_bounded_feasible
    a b x y hbd hx
  have hface : commonFaceDim a b x y ≤ F.card := by
    calc
      commonFaceDim a b x y ≤ commonFaceMinSubpresentationCount a b x y := hdimM
      _ = F.card := hFM.symm
  have hexcess := rowCircuit_selectedEffectiveRows_excess_defect_of_bounded
    a b x y hbd hx hcirc F hFint hface
  refine ⟨by simpa [F] using hFeq, ?_⟩
  have hexcess' := hexcess
  rw [hFM] at hexcess'
  simpa [F, circuitNeutralRows,
    HirschCommonFace.commonFaceDim, HirschCommonFace.commonDirection,
    HirschCommonFace.rowEvalMap, HirschCommonFace.commonSourceRows,
    commonFaceDim, commonDirection, rowEvalMap, commonSourceRows] using hexcess'

#print axioms rowCircuit_selectedEffectiveRows_defect_budget_of_bounded
#print axioms rowCircuit_selectedEffectiveRows_excess_defect_of_bounded
#print axioms rowCircuit_commonFace_minSubpresentation_excess_defect_of_bounded

end HirschCircuitLocalization
