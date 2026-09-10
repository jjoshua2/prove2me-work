import Mathlib
import Definitions.Def_Hirsch_model
import Solutions.PolynomialSeparatedRows
import Solutions.PolynomialGeodesicFaceCover

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 5000000

noncomputable section

namespace HirschBalancedFaceCover

variable {d n : ℕ}

/-- The supporting face cut out by one row of an H-presentation. -/
def rowSupportingFace
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (i : Fin n) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i}

/-- A row supporting hyperplane cuts out an extreme face of the H-polytope.
The face may be empty; no irredundancy assumption is needed. -/
lemma rowSupportingFace_isExtreme
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (i : Fin n) :
    IsExtreme ℝ (Hpoly a b) (rowSupportingFace a b i) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact hx.1
  · intro p hp q hq z hz hzopen
    refine ⟨hp, ?_⟩
    have hztight : ⟪a i, z⟫ = b i := hz.2
    have hp_le := hp i
    have hq_le := hq i
    obtain ⟨α, β, hα, hβ, hαβ, hzcomb⟩ := hzopen
    have hinner : ⟪a i, z⟫ = α * ⟪a i, p⟫ + β * ⟪a i, q⟫ := by
      rw [← hzcomb]
      simp [inner_add_right, inner_smul_right]
    by_contra hptight
    have hp_lt : ⟪a i, p⟫ < b i := lt_of_le_of_ne hp_le hptight
    have h1 : α * ⟪a i, p⟫ < α * b i :=
      mul_lt_mul_of_pos_left hp_lt hα
    have h2 : β * ⟪a i, q⟫ ≤ β * b i :=
      mul_le_mul_of_nonneg_left hq_le hβ.le
    have hb : α * b i + β * b i = b i := by
      rw [← add_mul, hαβ, one_mul]
    linarith

/-- Zero normals do not count toward the vertex-incidence multiplicity, so we
replace their row faces by the empty face. -/
def nonzeroRowFace
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (i : Fin n) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  if a i = 0 then ∅ else rowSupportingFace a b i

lemma nonzeroRowFace_isExtreme
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (i : Fin n) :
    IsExtreme ℝ (Hpoly a b) (nonzeroRowFace a b i) := by
  classical
  by_cases hai : a i = 0
  · rw [nonzeroRowFace, if_pos hai]
    refine ⟨by simp, ?_⟩
    intro p hp q hq z hz hzopen
    simpa using hz
  · rw [nonzeroRowFace, if_neg hai]
    exact rowSupportingFace_isExtreme a b i

/-- Every vertex is incident to at least `d` of the nonzero row faces. -/
lemma vertex_nonzero_row_face_multiplicity
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b)) :
    d ≤ (Finset.univ.filter (fun i => x ∈ nonzeroRowFace a b i)).card := by
  classical
  have h := HirschPolynomialAccess.nonzero_tight_rows_card_ge_dim a b x hx
  simpa [nonzeroRowFace, rowSupportingFace, hx.1] using h

/-- Balanced row-face cover bound.

For a `2*d`-row H-polytope, every path vertex is covered by at least `d`
nonzero row faces. Hence shortest-path double counting bounds the parent graph
diameter by the *average* row-face budget rather than by `d` times a worst
face budget. This is the incidence gain specific to the balanced/d-step
regime. -/
theorem balanced_diamLE_of_row_face_bounds
    (d : ℕ) (hd : 0 < d)
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d))
    (b : Fin (2 * d) → ℝ)
    (B : Fin (2 * d) → ℕ)
    (hFD : ∀ i, DiamLE (nonzeroRowFace a b i) (B i))
    (hconnect : ∀ u ∈ extremePoints ℝ (Hpoly a b),
      ∀ v ∈ extremePoints ℝ (Hpoly a b),
        ∃ L, HirschFaceSplice.Walk (Hpoly a b) L u v) :
    DiamLE (Hpoly a b) ((∑ i, (B i + 1)) / d - 1) := by
  apply HirschFaceSplice.diamLE_of_face_cover
    d d hd (Hpoly a b) (nonzeroRowFace a b) B
    (nonzeroRowFace_isExtreme a b) hFD
  · intro x hx
    exact vertex_nonzero_row_face_multiplicity a b x hx
  · exact hconnect

#print axioms rowSupportingFace_isExtreme
#print axioms nonzeroRowFace_isExtreme
#print axioms vertex_nonzero_row_face_multiplicity
#print axioms balanced_diamLE_of_row_face_bounds

end HirschBalancedFaceCover
