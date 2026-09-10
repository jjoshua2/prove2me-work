import Mathlib
import Solutions.CircuitIrredundantModel
import Solutions.PolynomialCircuitSubpresentationExcess
import Solutions.PolynomialCircuitDefectPublicBridge

open scoped RealInnerProductSpace InnerProduct
open Set Module Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCircuitLocalization

open HirschPolynomialAccess

variable {d n : ℕ}

/-- A row active at both endpoints vanishes after restricting to the common
direction and writing that restriction in common-face coordinates. -/
theorem commonFaceA_eq_zero_of_commonSourceRow
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) (i : Fin n)
    (hi : i ∈ commonSourceRows a b u v) :
    commonFaceA a b u v i = 0 := by
  let q := commonFaceA a b u v i
  have hqdir : commonFaceLift a b u v q ∈ commonDirection a b u v :=
    commonFaceLift_mem_direction a b u v q
  have hzero :
      rowEvalMap a (commonSourceRows a b u v)
          (commonFaceLift a b u v q) = 0 := by
    apply LinearMap.mem_ker.1
    simpa [commonDirection] using hqdir
  have hcoord := congrFun hzero ⟨i, hi⟩
  have hself : ⟪commonFaceA a b u v i, commonFaceA a b u v i⟫ = 0 := by
    rw [commonFace_inner_restricted]
    exact hcoord
  exact inner_self_eq_zero.mp hself

/-- The coordinate images of the two endpoints are separated by every row
whose restricted normal is nonzero. A row tight at both endpoints is a common
source row, hence has zero restricted normal by the preceding lemma. -/
theorem commonFace_coord_endpoint_separation
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b) (hv : v ∈ Hpoly a b) :
    ∃ q : EuclideanSpace ℝ (Fin (commonFaceDim a b u v)),
      q ∈ Hpoly (commonFaceA a b u v) (commonFaceB a b u v) ∧
      commonFacePoint a b u v q = v ∧
      ∀ i, commonFaceA a b u v i ≠ 0 →
        ⟪commonFaceA a b u v i, 0⟫ ≠ commonFaceB a b u v i ∨
        ⟪commonFaceA a b u v i, q⟫ ≠ commonFaceB a b u v i := by
  have hvF : v ∈ commonFace a b u v := commonFace_x_mem a b u v hv
  obtain ⟨q, hq, hpoint⟩ := commonFacePoint_surjOn a b u v hvF
  refine ⟨q, hq, hpoint, ?_⟩
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

/-- The canonical common-face coordinate H-polyhedron admits an equivalent
subpresentation that is irredundant in the exact predicate used by the open
circuit-to-edge refinement theorem and has a strict feasible point. -/
theorem commonFace_coord_irredundant_strict_subpresentation
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b) (hv : v ∈ Hpoly a b) :
    ∃ m : ℕ, m ≤ n ∧ ∃ e : Fin m ↪ Fin n,
      Hpoly
          (fun j => commonFaceA a b u v (e j))
          (fun j => commonFaceB a b u v (e j)) =
        Hpoly (commonFaceA a b u v) (commonFaceB a b u v) ∧
      RowPresentationIrredundant
          (fun j => commonFaceA a b u v (e j))
          (fun j => commonFaceB a b u v (e j)) ∧
      StrictlyFeasibleRows
          (fun j => commonFaceA a b u v (e j))
          (fun j => commonFaceB a b u v (e j)) := by
  have huF : u ∈ commonFace a b u v := commonFace_u_mem a b u v hu
  have hzero :
      (0 : EuclideanSpace ℝ (Fin (commonFaceDim a b u v))) ∈
        Hpoly (commonFaceA a b u v) (commonFaceB a b u v) := by
    apply (mem_commonFace_coord_iff a b u v 0).2
    simpa [commonFacePoint] using huF
  obtain ⟨q, hq, _hpoint, hsep⟩ :=
    commonFace_coord_endpoint_separation a b u v hu hv
  exact HirschCircuit.exists_irredundant_strict_model
    (commonFaceDim a b u v) n
    (commonFaceA a b u v) (commonFaceB a b u v)
    0 q hzero hq hsep

/-- Strong common-face normalization for a vertex-to-vertex ambient row
circuit.  The same equivalent restricted-row presentation is simultaneously
irredundant, strictly feasible, and charged by the ambient facet-excess budget:

`(m - h) + selected neutral-rank defect ≤ n - d`.

This is tailored to the hypotheses of `polynomial_edge_refinement_of_circuit_walks`:
a recursive/common-face routing argument may work with a bona fide irredundant,
strict row model rather than a padded presentation. -/
theorem rowCircuit_commonFace_irredundant_strict_excess_defect
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u)) :
    ∃ m : ℕ, m ≤ n ∧ ∃ e : Fin m ↪ Fin n,
      Hpoly
          (fun j => commonFaceA a b u v (e j))
          (fun j => commonFaceB a b u v (e j)) =
        Hpoly (commonFaceA a b u v) (commonFaceB a b u v) ∧
      RowPresentationIrredundant
          (fun j => commonFaceA a b u v (e j))
          (fun j => commonFaceB a b u v (e j)) ∧
      StrictlyFeasibleRows
          (fun j => commonFaceA a b u v (e j))
          (fun j => commonFaceB a b u v (e j)) ∧
      let F : Finset (Fin n) := Finset.univ.map e
      (m - commonFaceDim a b u v) +
          ((commonFaceDim a b u v - 1) -
            Module.finrank ℝ
              (((rowEvalMap a
                (F ∩ circuitNeutralRows a (v - u))).domRestrict
                (commonDirection a b u v)).range)) ≤
        n - d := by
  classical
  obtain ⟨m, hm, e, he, hirr, hstrict⟩ :=
    commonFace_coord_irredundant_strict_subpresentation
      a b u v hu.1 hv.1
  refine ⟨m, hm, e, he, hirr, hstrict, ?_⟩
  let F : Finset (Fin n) := Finset.univ.map e
  have hzeroFull :
      (0 : EuclideanSpace ℝ (Fin (commonFaceDim a b u v))) ∈
        Hpoly (commonFaceA a b u v) (commonFaceB a b u v) := by
    apply (mem_commonFace_coord_iff a b u v 0).2
    simpa [commonFacePoint] using commonFace_u_mem a b u v hu.1
  have hzeroSub :
      (0 : EuclideanSpace ℝ (Fin (commonFaceDim a b u v))) ∈
        Hpoly
          (fun j => commonFaceA a b u v (e j))
          (fun j => commonFaceB a b u v (e j)) := by
    rw [he]
    exact hzeroFull
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
  have h0extFull :
      (0 : EuclideanSpace ℝ (Fin (commonFaceDim a b u v))) ∈
        extremePoints ℝ
          (Hpoly (commonFaceA a b u v) (commonFaceB a b u v)) := by
    simpa [HirschCommonFace.commonFaceDim,
      HirschCommonFace.commonDirection, HirschCommonFace.commonSourceRows,
      HirschCommonFace.rowEvalMap,
      HirschCommonFace.commonFaceA, HirschCommonFace.commonFaceB,
      HirschCommonFace.commonFaceLiftCLM, HirschCommonFace.commonFaceLift,
      HirschCommonFace.commonFaceRepr] using
      commonFace_coord_zero_extreme a b u v hu
  have h0extSub :
      (0 : EuclideanSpace ℝ (Fin (commonFaceDim a b u v))) ∈
        extremePoints ℝ
          (Hpoly
            (fun j => commonFaceA a b u v (e j))
            (fun j => commonFaceB a b u v (e j))) := by
    rw [he]
    exact h0extFull
  have hface : commonFaceDim a b u v ≤ m :=
    rows_ge_dimension_of_vertex
      (fun j => commonFaceA a b u v (e j))
      (fun j => commonFaceB a b u v (e j)) 0 h0extSub
  have hfaceF : commonFaceDim a b u v ≤ F.card := by
    simpa [F] using hface
  have hdn : d ≤ n := rows_ge_dimension_of_vertex a b u hu
  have hexcess := rowCircuit_selectedEffectiveRows_excess_defect
    a b u v hu hcirc F hFint hfaceF hdn
  simpa [F] using hexcess

#print axioms commonFaceA_eq_zero_of_commonSourceRow
#print axioms commonFace_coord_endpoint_separation
#print axioms commonFace_coord_irredundant_strict_subpresentation
#print axioms rowCircuit_commonFace_irredundant_strict_excess_defect

end HirschCircuitLocalization
