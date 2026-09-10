import Mathlib
import Definitions.Def_Hirsch_common_face_geometry
import Solutions.PolynomialCircuitSubpresentationExcess

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCircuitLocalization

open HirschPolynomialAccess

variable {d n : ℕ}

/-- The full common-face coordinate presentation is itself a subpresentation,
so the set of admissible row budgets is nonempty. -/
theorem commonFace_subpresentation_exists
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) :
    ∃ M : ℕ, HirschCommonFace.CommonFaceHasSubpresentationAtMost a b u v M := by
  refine ⟨n, ?_⟩
  change HirschCommonFace.HasSubpresentationAtMost
    (HirschCommonFace.commonFaceA a b u v)
    (HirschCommonFace.commonFaceB a b u v) n
  let e : Fin n ↪ Fin n := ⟨fun i => i, by intro i j h; exact h⟩
  refine ⟨n, le_rfl, e, ?_⟩
  rfl

/-- Least number of original common-face coordinate rows sufficient to give an
equivalent H-presentation.  This is an intrinsic *row-presentation* count; no
identification with geometric facets is built into the definition. -/
noncomputable def commonFaceMinSubpresentationCount
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) : ℕ := by
  classical
  exact Nat.find (commonFace_subpresentation_exists a b u v)

theorem commonFaceMinSubpresentation_spec
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) :
    HirschCommonFace.CommonFaceHasSubpresentationAtMost a b u v
      (commonFaceMinSubpresentationCount a b u v) := by
  classical
  exact Nat.find_spec (commonFace_subpresentation_exists a b u v)

theorem commonFaceMinSubpresentation_le
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) (M : ℕ)
    (hM : HirschCommonFace.CommonFaceHasSubpresentationAtMost a b u v M) :
    commonFaceMinSubpresentationCount a b u v ≤ M := by
  classical
  exact Nat.find_min' (commonFace_subpresentation_exists a b u v) hM

/-- If zero is feasible, then after selecting a subpresentation one may discard
all selected rows whose normal is zero and reindex the remaining rows without
changing the represented H-polyhedron.  Zero-normal selected inequalities are
tautologies because feasibility of zero gives nonnegative right-hand side. -/
theorem effective_subpresentation_preserves_hpoly
    {r N m : ℕ}
    (A : Fin N → EuclideanSpace ℝ (Fin r)) (B : Fin N → ℝ)
    (hzero : (0 : EuclideanSpace ℝ (Fin r)) ∈ Hpoly A B)
    (e : Fin m ↪ Fin N) :
    let F : Finset (Fin N) :=
      (Finset.univ.map e) ∩ Finset.univ.filter (fun i => A i ≠ 0)
    ∃ eF : Fin F.card ↪ Fin N,
      Hpoly (fun j => A (eF j)) (fun j => B (eF j)) =
        Hpoly (fun j => A (e j)) (fun j => B (e j)) := by
  classical
  let F : Finset (Fin N) :=
    (Finset.univ.map e) ∩ Finset.univ.filter (fun i => A i ≠ 0)
  let q : Fin F.card ≃ {i : Fin N // i ∈ F} :=
    (Fintype.equivFinOfCardEq (α := {i : Fin N // i ∈ F}) (by simp)).symm
  let eF : Fin F.card ↪ Fin N :=
    ⟨fun j => (q j).1, by
      intro j k hjk
      apply q.injective
      exact Subtype.ext hjk⟩
  refine ⟨eF, ?_⟩
  ext x
  constructor
  · intro hx j
    by_cases hA : A (e j) = 0
    · have hz := hzero (e j)
      simpa [hA] using hz
    · have hiF : e j ∈ F := by
        refine Finset.mem_inter.2 ⟨?_, ?_⟩
        · simp
        · simp [hA]
      let z : {i : Fin N // i ∈ F} := ⟨e j, hiF⟩
      obtain ⟨k, hk⟩ := q.surjective z
      have hkval : eF k = e j := by
        change (q k).1 = e j
        exact congrArg Subtype.val hk
      have hxk := hx k
      simpa [hkval] using hxk
  · intro hx k
    have hkF : (q k).1 ∈ F := (q k).property
    have hkMap : (q k).1 ∈ Finset.univ.map e :=
      (Finset.mem_inter.1 hkF).1
    obtain ⟨j, _hj, hjeq⟩ := Finset.mem_map.1 hkMap
    have hxj := hx j
    have hval : e j = eF k := by
      change e j = (q k).1
      exact hjeq
    simpa [hval] using hxj

/-- A witness at the least common-face row budget can be chosen so that every
selected row is effective.  Consequently its effective selected-row set has
cardinality exactly the minimum row-presentation count. -/
theorem commonFace_minSubpresentation_effective_witness
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b)) :
    let M := commonFaceMinSubpresentationCount a b u v
    ∃ e : Fin M ↪ Fin n,
      Hpoly
          (fun j => HirschCommonFace.commonFaceA a b u v (e j))
          (fun j => HirschCommonFace.commonFaceB a b u v (e j)) =
        Hpoly
          (HirschCommonFace.commonFaceA a b u v)
          (HirschCommonFace.commonFaceB a b u v) ∧
      let F : Finset (Fin n) :=
        (Finset.univ.map e) ∩ HirschCommonFace.commonFaceEffectiveRows a b u v
      F.card = M ∧ HirschCommonFace.commonFaceDim a b u v ≤ M := by
  classical
  let M := commonFaceMinSubpresentationCount a b u v
  have hspec := commonFaceMinSubpresentation_spec a b u v
  change HirschCommonFace.HasSubpresentationAtMost
    (HirschCommonFace.commonFaceA a b u v)
    (HirschCommonFace.commonFaceB a b u v) M at hspec
  obtain ⟨m, hm, e, he⟩ := hspec
  have hAtm : HirschCommonFace.CommonFaceHasSubpresentationAtMost a b u v m := by
    change HirschCommonFace.HasSubpresentationAtMost
      (HirschCommonFace.commonFaceA a b u v)
      (HirschCommonFace.commonFaceB a b u v) m
    exact ⟨m, le_rfl, e, he⟩
  have hMle : M ≤ m := by
    simpa [M] using commonFaceMinSubpresentation_le a b u v m hAtm
  have hmeq : m = M := Nat.le_antisymm hm hMle
  subst m
  refine ⟨e, he, ?_⟩
  let F : Finset (Fin n) :=
    (Finset.univ.map e) ∩ HirschCommonFace.commonFaceEffectiveRows a b u v
  have hFle : F.card ≤ M := by
    calc
      F.card ≤ (Finset.univ.map e).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = M := by simp
  have hzero :
      (0 : EuclideanSpace ℝ (Fin (HirschPolynomialAccess.commonFaceDim a b u v))) ∈
        Hpoly
          (HirschCommonFace.commonFaceA a b u v)
          (HirschCommonFace.commonFaceB a b u v) := by
    have hzext := commonFace_coord_zero_extreme a b u v hu
    simpa [HirschCommonFace.commonFaceDim, HirschPolynomialAccess.commonFaceDim,
      HirschCommonFace.commonDirection, HirschCommonFace.commonSourceRows,
      HirschCommonFace.rowEvalMap, HirschPolynomialAccess.commonDirection,
      HirschPolynomialAccess.rowEvalMap, HirschPolynomialAccess.commonSourceRows,
      HirschCommonFace.commonFaceA, HirschCommonFace.commonFaceB,
      HirschCommonFace.commonFaceLiftCLM, HirschCommonFace.commonFaceLift,
      HirschCommonFace.commonFaceRepr,
      HirschPolynomialAccess.commonFaceA, HirschPolynomialAccess.commonFaceB,
      HirschPolynomialAccess.commonFaceLiftCLM, HirschPolynomialAccess.commonFaceLift,
      HirschPolynomialAccess.commonFaceRepr] using hzext.1
  obtain ⟨eF, heF⟩ := effective_subpresentation_preserves_hpoly
    (HirschCommonFace.commonFaceA a b u v)
    (HirschCommonFace.commonFaceB a b u v) hzero e
  have hAtF : HirschCommonFace.CommonFaceHasSubpresentationAtMost a b u v F.card := by
    change HirschCommonFace.HasSubpresentationAtMost
      (HirschCommonFace.commonFaceA a b u v)
      (HirschCommonFace.commonFaceB a b u v) F.card
    refine ⟨F.card, le_rfl, eF, ?_⟩
    have hsameF :
        (Finset.univ.map e) ∩
            Finset.univ.filter
              (fun i => HirschCommonFace.commonFaceA a b u v i ≠ 0) = F := by
      rfl
    simpa [hsameF] using heF.trans he
  have hMleF : M ≤ F.card := by
    simpa [M] using commonFaceMinSubpresentation_le a b u v F.card hAtF
  have hFeq : F.card = M := Nat.le_antisymm hFle hMleF
  have hdimF : HirschCommonFace.commonFaceDim a b u v ≤ F.card := by
    simpa [F] using
      commonFace_subpresentation_effectiveRows_card_ge_dim
        a b u v hu M e he
  have hdimM : HirschCommonFace.commonFaceDim a b u v ≤ M := by
    calc
      HirschCommonFace.commonFaceDim a b u v ≤ F.card := hdimF
      _ = M := hFeq
  exact ⟨hFeq, by simpa [M] using hdimM⟩

/-- Exact intrinsic row-presentation version of the common-face circuit
excess/defect inequality.  The excess term uses the *least* number `M` of
original coordinate inequalities giving an equivalent common-face
H-presentation, rather than an arbitrary upper-bound presentation. -/
theorem rowCircuit_commonFace_minSubpresentation_excess_defect
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u)) :
    let M := commonFaceMinSubpresentationCount a b u v
    ∃ e : Fin M ↪ Fin n,
      Hpoly
          (fun j => HirschCommonFace.commonFaceA a b u v (e j))
          (fun j => HirschCommonFace.commonFaceB a b u v (e j)) =
        Hpoly
          (HirschCommonFace.commonFaceA a b u v)
          (HirschCommonFace.commonFaceB a b u v) ∧
      let F : Finset (Fin n) :=
        (Finset.univ.map e) ∩ HirschCommonFace.commonFaceEffectiveRows a b u v
      F.card = M ∧
      (M - HirschCommonFace.commonFaceDim a b u v) +
          ((HirschCommonFace.commonFaceDim a b u v - 1) -
            Module.finrank ℝ
              (((HirschCommonFace.rowEvalMap a
                (F ∩ Finset.univ.filter (fun i =>
                  a i ≠ 0 ∧ ⟪a i, v - u⟫ = 0))).domRestrict
                (HirschCommonFace.commonDirection a b u v)).range)) ≤
        n - d := by
  classical
  let M := commonFaceMinSubpresentationCount a b u v
  obtain ⟨e, he, hFeq, hdimM⟩ :=
    commonFace_minSubpresentation_effective_witness a b u v hu
  refine ⟨e, he, ?_⟩
  let F : Finset (Fin n) :=
    (Finset.univ.map e) ∩ HirschCommonFace.commonFaceEffectiveRows a b u v
  have hFM : F.card = commonFaceMinSubpresentationCount a b u v := by
    simpa [F] using hFeq
  have hFpub : F ⊆ HirschCommonFace.commonFaceEffectiveRows a b u v :=
    Finset.inter_subset_right
  have hFint :
      F ⊆ effectiveRowsOnSubspace a (commonDirection a b u v) := by
    rw [effectiveRowsOn_commonDirection_eq_publicCommonFaceEffectiveRows]
    exact hFpub
  have hpubFace : HirschCommonFace.commonFaceDim a b u v ≤ F.card := by
    calc
      HirschCommonFace.commonFaceDim a b u v ≤
          commonFaceMinSubpresentationCount a b u v := hdimM
      _ = F.card := hFM.symm
  have hfaceInternal : commonFaceDim a b u v ≤ F.card := by
    simpa [HirschCommonFace.commonFaceDim,
      HirschPolynomialAccess.commonFaceDim,
      HirschCommonFace.commonDirection, HirschCommonFace.commonSourceRows,
      HirschCommonFace.rowEvalMap,
      HirschPolynomialAccess.commonDirection,
      HirschPolynomialAccess.rowEvalMap,
      HirschPolynomialAccess.commonSourceRows] using hpubFace
  have hdn : d ≤ n := rows_ge_dimension_of_vertex a b u hu
  have hexcess := rowCircuit_selectedEffectiveRows_excess_defect
    a b u v hu hcirc F hFint hfaceInternal hdn
  refine ⟨by simpa [F] using hFeq, ?_⟩
  have hexcess' := hexcess
  rw [hFM] at hexcess'
  simpa [F, circuitNeutralRows,
    HirschCommonFace.commonFaceDim, HirschCommonFace.commonDirection,
    HirschCommonFace.rowEvalMap, HirschCommonFace.commonSourceRows,
    HirschPolynomialAccess.commonFaceDim, HirschPolynomialAccess.commonDirection,
    HirschPolynomialAccess.rowEvalMap, HirschPolynomialAccess.commonSourceRows] using hexcess'

#print axioms commonFace_subpresentation_exists
#print axioms commonFaceMinSubpresentation_spec
#print axioms commonFaceMinSubpresentation_le
#print axioms effective_subpresentation_preserves_hpoly
#print axioms commonFace_minSubpresentation_effective_witness
#print axioms rowCircuit_commonFace_minSubpresentation_excess_defect

end HirschCircuitLocalization
