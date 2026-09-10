import Mathlib
import Solutions.CircuitPhaseRoute
import Solutions.PolynomialCommonFaceRoutingModel

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCircuit

/-- The completed Natura standard-form route gives an explicit cubic
row-circuit walk on the *same* bounded H-presentation.  No irredundancy,
strict-feasibility, or endpoint-separation hypothesis is needed for this
fixed-presentation form. -/
theorem rowCircuitWalk_explicit_cubic_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    RowCircuitWalk a b (17 * n ^ 3) u v := by
  have hinj := rowMap_injective_of_bounded a b hbd u hu.1
  have hsu := slack_mem_extremePoints_of_mem_extremePoints a b hinj u hu
  have hsv := slack_mem_extremePoints_of_mem_extremePoints a b hinj v hv
  rw [slackPoly_eq_standardSlice] at hsu hsv
  have hw := standardCircuitWalk_cubic
    (LinearMap.range (rowMap a)) b
    (slack a b u) (slack a b v) hsu.1 hsv
  exact (bounded_rowCircuitWalk_iff_standardCircuitWalk
    a b hbd u hu.1 (17 * n ^ 3) u v).mpr hw

#print axioms rowCircuitWalk_explicit_cubic_of_bounded

end HirschCircuit

namespace HirschCircuitLocalization

open HirschPolynomialAccess

variable {d n : ℕ}

/-- The edge-refinement-ready common-face model from the rank/defect work also
carries an explicit `17*m^3` row-circuit walk between the two coordinate
vertices, on the very same selected-row presentation. -/
theorem commonFace_edgeRefinement_ready_with_cubic_circuitWalk
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
        commonFacePoint a b u v q = v ∧
        RowCircuitWalk
          (fun j => commonFaceA a b u v (e j))
          (fun j => commonFaceB a b u v (e j))
          (17 * m ^ 3) 0 q := by
  obtain ⟨m, hm, e, q, he, hbdSub, hirr, hstrict,
      h0ext, hqext, hpoint⟩ :=
    commonFace_edgeRefinement_ready_model a b u v hbd hu hv
  have hwalk := HirschCircuit.rowCircuitWalk_explicit_cubic_of_bounded
    (fun j => commonFaceA a b u v (e j))
    (fun j => commonFaceB a b u v (e j))
    hbdSub 0 q h0ext hqext
  exact ⟨m, hm, e, q, he, hbdSub, hirr, hstrict,
    h0ext, hqext, hpoint, hwalk⟩

/-- For an ambient vertex-to-vertex row circuit, one can simultaneously choose
a lower-dimensional common-face presentation which is bounded, irredundant,
strictly feasible, has the two endpoint coordinates as vertices, has an
explicit cubic row-circuit walk between them, and obeys the ambient
excess/neutral-rank-defect charge.

Thus after common-face localization, **circuit-walk existence and presentation
cleanup are both discharged on the same model**.  The remaining dynamic
bottleneck is converting such a row-circuit walk to ordinary edge/stay steps. -/
theorem rowCircuit_commonFace_ready_with_cubic_walk_excess_defect
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
        RowCircuitWalk
          (fun j => commonFaceA a b u v (e j))
          (fun j => commonFaceB a b u v (e j))
          (17 * m ^ 3) 0 q ∧
        let F : Finset (Fin n) := Finset.univ.map e
        (m - commonFaceDim a b u v) +
            ((commonFaceDim a b u v - 1) -
              Module.finrank ℝ
                (((rowEvalMap a
                  (F ∩ circuitNeutralRows a (v - u))).domRestrict
                  (commonDirection a b u v)).range)) ≤
          n - d := by
  obtain ⟨m, hm, e, q, he, hbdSub, hirr, hstrict,
      h0ext, hqext, hpoint, hdefect⟩ :=
    rowCircuit_commonFace_edgeRefinement_ready_excess_defect
      a b u v hbd hu hv hcirc
  have hwalk := HirschCircuit.rowCircuitWalk_explicit_cubic_of_bounded
    (fun j => commonFaceA a b u v (e j))
    (fun j => commonFaceB a b u v (e j))
    hbdSub 0 q h0ext hqext
  exact ⟨m, hm, e, q, he, hbdSub, hirr, hstrict,
    h0ext, hqext, hpoint, hwalk, hdefect⟩

#print axioms commonFace_edgeRefinement_ready_with_cubic_circuitWalk
#print axioms rowCircuit_commonFace_ready_with_cubic_walk_excess_defect

end HirschCircuitLocalization
