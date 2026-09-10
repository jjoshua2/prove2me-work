import Mathlib
import Solutions.PolynomialCommonFaceIrredundantModel

open scoped RealInnerProductSpace InnerProduct Convex
open Set Module Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCircuitLocalization

open HirschPolynomialAccess

variable {d n : ℕ}

/-- An ambient extreme point lying in the common face remains extreme after
passing to the canonical common-face coordinates.  The coordinate map is affine
with injective linear part, so any nontrivial open segment through the coordinate
point would lift to a nontrivial open segment through the ambient vertex. -/
theorem commonFace_coord_extreme_of_parent_extreme
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (z : EuclideanSpace ℝ (Fin (commonFaceDim a b u v)))
    (hz : z ∈ Hpoly (commonFaceA a b u v) (commonFaceB a b u v))
    (hparent : commonFacePoint a b u v z ∈ extremePoints ℝ (Hpoly a b)) :
    z ∈ extremePoints ℝ
      (Hpoly (commonFaceA a b u v) (commonFaceB a b u v)) := by
  refine ⟨hz, ?_⟩
  intro p hp q hq hseg
  have hpP : commonFacePoint a b u v p ∈ Hpoly a b :=
    ((mem_commonFace_coord_iff a b u v p).1 hp).1
  have hqP : commonFacePoint a b u v q ∈ Hpoly a b :=
    ((mem_commonFace_coord_iff a b u v q).1 hq).1
  obtain ⟨α, β, hα, hβ, hαβ, hcomb⟩ := hseg
  have hzSeg :
      commonFacePoint a b u v z ∈ openSegment ℝ
        (commonFacePoint a b u v p)
        (commonFacePoint a b u v q) := by
    refine ⟨α, β, hα, hβ, hαβ, ?_⟩
    calc
      α • commonFacePoint a b u v p +
          β • commonFacePoint a b u v q =
        (α + β) • u +
          commonFaceLift a b u v (α • p + β • q) := by
            simp [commonFacePoint, map_add, map_smul]
            module
      _ = commonFacePoint a b u v z := by
        rw [hαβ, hcomb]
        simp [commonFacePoint]
  have hpZ : commonFacePoint a b u v p = commonFacePoint a b u v z :=
    hparent.2 hpP hqP hzSeg
  exact commonFacePoint_injective a b u v hpZ

/-- The target ambient vertex has a coordinate representative which is an
extreme point of the common-face coordinate H-polyhedron. -/
theorem commonFace_coord_target_extreme
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    ∃ q : EuclideanSpace ℝ (Fin (commonFaceDim a b u v)),
      q ∈ extremePoints ℝ
        (Hpoly (commonFaceA a b u v) (commonFaceB a b u v)) ∧
      commonFacePoint a b u v q = v := by
  have hvF : v ∈ commonFace a b u v := commonFace_x_mem a b u v hv.1
  obtain ⟨q, hq, hpoint⟩ := commonFacePoint_surjOn a b u v hvF
  refine ⟨q, ?_, hpoint⟩
  apply commonFace_coord_extreme_of_parent_extreme a b u v q hq
  rw [hpoint]
  exact hv

/-- Static package needed to invoke the open circuit-to-edge refinement theorem
inside a common face.  Starting from two ambient vertices of a bounded
H-polyhedron, one obtains a lower-dimensional coordinate presentation using
original rows which is:

* exactly equivalent to the canonical common-face coordinate H-polyhedron,
* bounded,
* row-irredundant,
* strictly feasible,
* and has coordinate representatives of both endpoints as extreme points.

The source representative is `0`; `q` represents the target vertex. -/
theorem commonFace_edgeRefinement_ready_model
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    ∃ m : ℕ, m ≤ n ∧ ∃ e : Fin m ↪ Fin n,
      ∃ q : EuclideanSpace ℝ (Fin (commonFaceDim a b u v)),
        Hpoly
            (fun j => commonFaceA a b u v (e j))
            (fun j => commonFaceB a b u v (e j)) =
          Hpoly (commonFaceA a b u v) (commonFaceB a b u v) ∧
        Bornology.IsBounded
          (Hpoly
            (fun j => commonFaceA a b u v (e j))
            (fun j => commonFaceB a b u v (e j))) ∧
        RowPresentationIrredundant
          (fun j => commonFaceA a b u v (e j))
          (fun j => commonFaceB a b u v (e j)) ∧
        StrictlyFeasibleRows
          (fun j => commonFaceA a b u v (e j))
          (fun j => commonFaceB a b u v (e j)) ∧
        (0 : EuclideanSpace ℝ (Fin (commonFaceDim a b u v))) ∈
          extremePoints ℝ
            (Hpoly
              (fun j => commonFaceA a b u v (e j))
              (fun j => commonFaceB a b u v (e j))) ∧
        q ∈ extremePoints ℝ
          (Hpoly
            (fun j => commonFaceA a b u v (e j))
            (fun j => commonFaceB a b u v (e j))) ∧
        commonFacePoint a b u v q = v := by
  have huF : u ∈ commonFace a b u v := commonFace_u_mem a b u v hu.1
  have hzero :
      (0 : EuclideanSpace ℝ (Fin (commonFaceDim a b u v))) ∈
        Hpoly (commonFaceA a b u v) (commonFaceB a b u v) := by
    apply (mem_commonFace_coord_iff a b u v 0).2
    simpa [commonFacePoint] using huF
  obtain ⟨q, hqExt, hpoint⟩ := commonFace_coord_target_extreme a b u v hv
  have hq : q ∈ Hpoly (commonFaceA a b u v) (commonFaceB a b u v) := hqExt.1
  obtain ⟨_q', _hq', _hpoint', hsep⟩ :=
    commonFace_coord_endpoint_separation a b u v hu.1 hv.1
  have hsepq : ∀ i, commonFaceA a b u v i ≠ 0 →
      ⟪commonFaceA a b u v i, 0⟫ ≠ commonFaceB a b u v i ∨
      ⟪commonFaceA a b u v i, q⟫ ≠ commonFaceB a b u v i := by
    intro i hAi
    by_cases h0 : ⟪commonFaceA a b u v i, 0⟫ ≠ commonFaceB a b u v i
    · exact Or.inl h0
    · right
      intro hqeq
      have h0eq : ⟪commonFaceA a b u v i, 0⟫ = commonFaceB a b u v i :=
        not_ne_iff.mp h0
      have hui : ⟪a i, u⟫ = b i := by
        simp only [inner_zero_right] at h0eq
        dsimp [commonFaceB] at h0eq
        linarith
      have hlift : commonFaceLift a b u v q = v - u := by
        have hp := congrArg (fun z => z - u) hpoint
        simpa [commonFacePoint] using hp
      have hvi : ⟪a i, v⟫ = b i := by
        rw [commonFace_inner_restricted, hlift, inner_sub_right] at hqeq
        dsimp [commonFaceB] at hqeq
        linarith
      have hai : a i ≠ 0 := by
        intro hai0
        apply hAi
        simp [commonFaceA, commonFaceLiftCLM, hai0]
      have hiC : i ∈ commonSourceRows a b u v := by
        simp [commonSourceRows, hai, hui, hvi]
      exact hAi (commonFaceA_eq_zero_of_commonSourceRow a b u v i hiC)
  obtain ⟨m, hm, e, he, hirr, hstrict⟩ :=
    HirschCircuit.exists_irredundant_strict_model
      (commonFaceDim a b u v) n
      (commonFaceA a b u v) (commonFaceB a b u v)
      0 q hzero hq hsepq
  refine ⟨m, hm, e, q, he, ?_, hirr, hstrict, ?_, ?_, hpoint⟩
  · rw [he]
    exact commonFace_coord_bounded a b u v hbd
  · rw [he]
    simpa [HirschCommonFace.commonFaceDim,
      HirschCommonFace.commonDirection, HirschCommonFace.commonSourceRows,
      HirschCommonFace.rowEvalMap,
      HirschCommonFace.commonFaceA, HirschCommonFace.commonFaceB,
      HirschCommonFace.commonFaceLiftCLM, HirschCommonFace.commonFaceLift,
      HirschCommonFace.commonFaceRepr] using
      commonFace_coord_zero_extreme a b u v hu
  · rw [he]
    exact hqExt

/-- Edge-refinement-ready common-face package with the circuit defect/excess
charge attached to the very same irredundant, strictly feasible presentation.
No circuit-inheritance claim is made: the last summand records exactly how much
neutral rank was lost when the common face was normalized. -/
theorem rowCircuit_commonFace_edgeRefinement_ready_excess_defect
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u)) :
    ∃ m : ℕ, m ≤ n ∧ ∃ e : Fin m ↪ Fin n,
      ∃ q : EuclideanSpace ℝ (Fin (commonFaceDim a b u v)),
        Hpoly
            (fun j => commonFaceA a b u v (e j))
            (fun j => commonFaceB a b u v (e j)) =
          Hpoly (commonFaceA a b u v) (commonFaceB a b u v) ∧
        Bornology.IsBounded
          (Hpoly
            (fun j => commonFaceA a b u v (e j))
            (fun j => commonFaceB a b u v (e j))) ∧
        RowPresentationIrredundant
          (fun j => commonFaceA a b u v (e j))
          (fun j => commonFaceB a b u v (e j)) ∧
        StrictlyFeasibleRows
          (fun j => commonFaceA a b u v (e j))
          (fun j => commonFaceB a b u v (e j)) ∧
        (0 : EuclideanSpace ℝ (Fin (commonFaceDim a b u v))) ∈
          extremePoints ℝ
            (Hpoly
              (fun j => commonFaceA a b u v (e j))
              (fun j => commonFaceB a b u v (e j))) ∧
        q ∈ extremePoints ℝ
          (Hpoly
            (fun j => commonFaceA a b u v (e j))
            (fun j => commonFaceB a b u v (e j))) ∧
        commonFacePoint a b u v q = v ∧
        let F : Finset (Fin n) := Finset.univ.map e
        (m - commonFaceDim a b u v) +
            ((commonFaceDim a b u v - 1) -
              Module.finrank ℝ
                (((rowEvalMap a
                  (F ∩ circuitNeutralRows a (v - u))).domRestrict
                  (commonDirection a b u v)).range)) ≤
          n - d := by
  classical
  obtain ⟨m, hm, e, q, he, hbdSub, hirr, hstrict,
      h0ext, hqext, hpoint⟩ :=
    commonFace_edgeRefinement_ready_model a b u v hbd hu hv
  refine ⟨m, hm, e, q, he, hbdSub, hirr, hstrict, h0ext, hqext, hpoint, ?_⟩
  let F : Finset (Fin n) := Finset.univ.map e
  have hzeroSub :
      (0 : EuclideanSpace ℝ (Fin (commonFaceDim a b u v))) ∈
        Hpoly
          (fun j => commonFaceA a b u v (e j))
          (fun j => commonFaceB a b u v (e j)) := h0ext.1
  have hnonzero : ∀ j : Fin m, commonFaceA a b u v (e j) ≠ 0 :=
    HirschCircuit.irredundant_rows_nonzero_of_mem
      (fun j => commonFaceA a b u v (e j))
      (fun j => commonFaceB a b u v (e j)) hirr 0 hzeroSub
  have hFint : F ⊆ effectiveRowsOnSubspace a (commonDirection a b u v) := by
    rw [effectiveRowsOn_commonDirection_eq_coordinateEffectiveRows]
    intro i hiF
    obtain ⟨j, _hj, hji⟩ := Finset.mem_map.1 hiF
    subst i
    simp [hnonzero j]
  have hface : commonFaceDim a b u v ≤ m :=
    rows_ge_dimension_of_vertex
      (fun j => commonFaceA a b u v (e j))
      (fun j => commonFaceB a b u v (e j)) 0 h0ext
  have hfaceF : commonFaceDim a b u v ≤ F.card := by
    simpa [F] using hface
  have hdn : d ≤ n := rows_ge_dimension_of_vertex a b u hu
  have hexcess := rowCircuit_selectedEffectiveRows_excess_defect
    a b u v hu hcirc F hFint hfaceF hdn
  simpa [F] using hexcess

#print axioms commonFace_coord_extreme_of_parent_extreme
#print axioms commonFace_coord_target_extreme
#print axioms commonFace_edgeRefinement_ready_model
#print axioms rowCircuit_commonFace_edgeRefinement_ready_excess_defect

end HirschCircuitLocalization
