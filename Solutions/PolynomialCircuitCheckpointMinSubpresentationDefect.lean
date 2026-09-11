import Mathlib
import Solutions.PolynomialCircuitCheckpointLocalization
import Solutions.PolynomialCircuitSelectedRowDefect
import Solutions.PolynomialCommonFaceMinimalSubpresentation
import Solutions.CircuitSlackBounded

/-!
# Minimum-subpresentation excess/defect at nonvertex circuit checkpoints

The older minimum-presentation theorem required the circuit step to start at a
parent vertex.  The neutral-rank argument actually needs only one reference
vertex anywhere in the bounded parent, while feasibility of the checkpoint is
enough for the common-face coordinate model to be nonempty.  Boundedness then
forces its row map to be injective and supplies the missing `h ≤ M` count.
-/

open scoped BigOperators RealInnerProductSpace
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- The selected-effective-row defect budget does not require either checkpoint
to be a vertex.  A single reference vertex anywhere in the parent supplies the
rank-`d-1` neutral-row fact for an ambient row circuit. -/
theorem rowCircuit_selectedEffectiveRows_defect_budget_of_reference_vertex
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (z x y : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ extremePoints ℝ (Hpoly a b))
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
  have hgW : y - x ∈ W := by
    apply LinearMap.mem_ker.2
    funext i
    have hi := (Finset.mem_filter.1 i.2).2
    change ⟪a i.1, y - x⟫ = 0
    rw [inner_sub_right, hi.2.2, hi.2.1, sub_self]
  have hfullAmbient :
      Module.finrank ℝ (((rowEvalMap a Z).domRestrict W).range) =
        Module.finrank ℝ W - 1 := by
    simpa [Z, W] using
      rowCircuit_neutral_rank_on_subspace_eq_dim_sub_one
        a b z (y - x) hz hcirc W hgW
  have hfull :
      Module.finrank ℝ (((rowEvalMap a T).domRestrict W).range) =
        Module.finrank ℝ W - 1 := by
    calc
      Module.finrank ℝ (((rowEvalMap a T).domRestrict W).range) =
          Module.finrank ℝ (((rowEvalMap a Z).domRestrict W).range) := by
            simpa [T, Z, E] using restricted_rowEval_effective_rank_eq a W Z
      _ = Module.finrank ℝ W - 1 := hfullAmbient
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
  have hdel : (T \ S).card ≤ (E \ F).card := Finset.card_le_card hdelSub
  have hdefE :
      (Module.finrank ℝ W - 1) -
          Module.finrank ℝ (((rowEvalMap a S).domRestrict W).range) ≤
        (E \ F).card := hdef.trans hdel
  have hbudget : E.card + d ≤ n + Module.finrank ℝ W := by
    simpa [E, W, commonFaceDim] using
      commonDirection_effectiveRows_card_add_dim_le_rows_add_faceDim a b x y
  have hF' : F ⊆ E := by simpa [E, W] using hF
  have hcard : (E \ F).card + F.card = E.card :=
    Finset.card_sdiff_add_card_eq_card hF'
  have hmain :
      F.card +
          ((Module.finrank ℝ W - 1) -
            Module.finrank ℝ (((rowEvalMap a S).domRestrict W).range)) +
          d ≤ n + Module.finrank ℝ W := by
    omega
  simpa [S, Z, W, commonFaceDim] using hmain

/-- Traditional excess form of the same nonvertex checkpoint budget. -/
theorem rowCircuit_selectedEffectiveRows_excess_defect_of_reference_vertex
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (z x y : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (y - x))
    (F : Finset (Fin n))
    (hF : F ⊆ effectiveRowsOnSubspace a (commonDirection a b x y))
    (hface : commonFaceDim a b x y ≤ F.card)
    (hdn : d ≤ n) :
    (F.card - commonFaceDim a b x y) +
        ((commonFaceDim a b x y - 1) -
          Module.finrank ℝ
            (((rowEvalMap a (F ∩ circuitNeutralRows a (y - x))).domRestrict
              (commonDirection a b x y)).range)) ≤
      n - d := by
  have h := rowCircuit_selectedEffectiveRows_defect_budget_of_reference_vertex
    a b z x y hz hcirc F hF
  omega

/-- Minimality plus feasibility lets us choose a minimum-row common-face
subpresentation in which every selected row remains effective.  No checkpoint
vertex assumption is used. -/
theorem commonFace_minSubpresentation_effective_witness_of_feasible
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ Hpoly a b) :
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
      F.card = M := by
  classical
  let M := commonFaceMinSubpresentationCount a b x y
  have hspec := commonFaceMinSubpresentation_spec a b x y
  change HirschCommonFace.HasSubpresentationAtMost
    (HirschCommonFace.commonFaceA a b x y)
    (HirschCommonFace.commonFaceB a b x y) M at hspec
  obtain ⟨m, hm, e, he⟩ := hspec
  have hAtm : HirschCommonFace.CommonFaceHasSubpresentationAtMost a b x y m := by
    change HirschCommonFace.HasSubpresentationAtMost
      (HirschCommonFace.commonFaceA a b x y)
      (HirschCommonFace.commonFaceB a b x y) m
    exact ⟨m, le_rfl, e, he⟩
  have hMle : M ≤ m := by
    simpa [M] using commonFaceMinSubpresentation_le a b x y m hAtm
  have hmeq : m = M := Nat.le_antisymm hm hMle
  subst m
  refine ⟨e, he, ?_⟩
  let F : Finset (Fin n) :=
    (Finset.univ.map e) ∩ HirschCommonFace.commonFaceEffectiveRows a b x y
  have hFle : F.card ≤ M := by
    calc
      F.card ≤ (Finset.univ.map e).card := Finset.card_le_card Finset.inter_subset_left
      _ = M := by simp
  have hzero :
      (0 : EuclideanSpace ℝ (Fin (commonFaceDim a b x y))) ∈
        Hpoly (commonFaceA a b x y) (commonFaceB a b x y) := by
    apply (mem_commonFace_coord_iff a b x y 0).2
    have hxF := commonFace_u_mem a b x y hx
    simpa [commonFacePoint] using hxF
  obtain ⟨eF, heF⟩ := effective_subpresentation_preserves_hpoly
    (commonFaceA a b x y) (commonFaceB a b x y) hzero e
  have hAtF : HirschCommonFace.CommonFaceHasSubpresentationAtMost a b x y F.card := by
    change HirschCommonFace.HasSubpresentationAtMost
      (commonFaceA a b x y) (commonFaceB a b x y) F.card
    refine ⟨F.card, le_rfl, eF, ?_⟩
    have hsameF :
        (Finset.univ.map e) ∩ Finset.univ.filter (fun i => commonFaceA a b x y i ≠ 0) = F := by
      rfl
    simpa [hsameF] using heF.trans he
  have hMleF : M ≤ F.card := by
    simpa [M] using commonFaceMinSubpresentation_le a b x y F.card hAtF
  exact Nat.le_antisymm hFle hMleF

/-- Boundedness and source feasibility force the intrinsic common-face
dimension to be no larger than its minimum equivalent row-presentation count,
even when the checkpoint is not a vertex. -/
theorem commonFaceDim_le_minSubpresentation_of_bounded_feasible
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hx : x ∈ Hpoly a b) :
    commonFaceDim a b x y ≤ commonFaceMinSubpresentationCount a b x y := by
  classical
  let M := commonFaceMinSubpresentationCount a b x y
  have hspec := commonFaceMinSubpresentation_spec a b x y
  change HirschCommonFace.HasSubpresentationAtMost
    (commonFaceA a b x y) (commonFaceB a b x y) M at hspec
  obtain ⟨m, hm, e, he⟩ := hspec
  have hAtm : HirschCommonFace.CommonFaceHasSubpresentationAtMost a b x y m := by
    change HirschCommonFace.HasSubpresentationAtMost
      (commonFaceA a b x y) (commonFaceB a b x y) m
    exact ⟨m, le_rfl, e, he⟩
  have hMle : M ≤ m := by
    simpa [M] using commonFaceMinSubpresentation_le a b x y m hAtm
  have hmeq : m = M := Nat.le_antisymm hm hMle
  subst m
  have hbdCoord := commonFace_coord_bounded a b x y hbd
  have hbdSub : Bornology.IsBounded
      (Hpoly (fun j => commonFaceA a b x y (e j))
        (fun j => commonFaceB a b x y (e j))) := by
    rw [he]
    exact hbdCoord
  have hzero :
      (0 : EuclideanSpace ℝ (Fin (commonFaceDim a b x y))) ∈
        Hpoly (commonFaceA a b x y) (commonFaceB a b x y) := by
    apply (mem_commonFace_coord_iff a b x y 0).2
    have hxF := commonFace_u_mem a b x y hx
    simpa [commonFacePoint] using hxF
  have hzeroSub :
      (0 : EuclideanSpace ℝ (Fin (commonFaceDim a b x y))) ∈
        Hpoly (fun j => commonFaceA a b x y (e j))
          (fun j => commonFaceB a b x y (e j)) := by
    rw [he]
    exact hzero
  have hinj := HirschCircuit.rowMap_injective_of_bounded
    (fun j => commonFaceA a b x y (e j))
    (fun j => commonFaceB a b x y (e j)) hbdSub 0 hzeroSub
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [M, finrank_euclideanSpace_fin] using hdim

/-- Minimum-subpresentation excess/defect budget for a row-circuit displacement
between arbitrary checkpoints.  The source checkpoint need only be feasible;
one fixed parent vertex `z` supplies the ambient neutral-rank reference for all
steps of a circuit walk. -/
theorem rowCircuit_commonFace_minSubpresentation_excess_defect_checkpoint
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (z x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hz : z ∈ extremePoints ℝ (Hpoly a b))
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
  have hdn : d ≤ n := rows_ge_dimension_of_vertex a b z hz
  have hexcess := rowCircuit_selectedEffectiveRows_excess_defect_of_reference_vertex
    a b z x y hz hcirc F hFint hface hdn
  refine ⟨by simpa [F] using hFeq, ?_⟩
  have hexcess' := hexcess
  rw [hFM] at hexcess'
  simpa [F, circuitNeutralRows,
    HirschCommonFace.commonFaceDim, HirschCommonFace.commonDirection,
    HirschCommonFace.rowEvalMap, HirschCommonFace.commonSourceRows,
    commonFaceDim, commonDirection, rowEvalMap, commonSourceRows] using hexcess'

#print axioms rowCircuit_selectedEffectiveRows_defect_budget_of_reference_vertex
#print axioms rowCircuit_selectedEffectiveRows_excess_defect_of_reference_vertex
#print axioms commonFace_minSubpresentation_effective_witness_of_feasible
#print axioms commonFaceDim_le_minSubpresentation_of_bounded_feasible
#print axioms rowCircuit_commonFace_minSubpresentation_excess_defect_checkpoint

end HirschCircuitLocalization
