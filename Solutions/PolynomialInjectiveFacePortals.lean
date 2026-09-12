import Mathlib
import Solutions.PolynomialInjectiveHpolyVertexExistence
import Solutions.PolynomialCommonFace

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschPointed

variable {d n : ℕ}

/-- The face obtained by forcing a finite set of describing rows tight. -/
def rowTightFace
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (S : Finset (Fin n)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | x ∈ Hpoly a b ∧ ∀ i, i ∈ S → ⟪a i, x⟫ = b i}

/-- Encode `rowTightFace` by retaining every original row and appending the
reverse inequality for selected rows (and a zero tautology for unselected
rows).  Keeping the full original row block makes row-map injectivity immediate. -/
def rowTightFaceNormals
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (S : Finset (Fin n)) :
    Fin (n + n) → EuclideanSpace ℝ (Fin d) :=
  Fin.append a (fun i => if i ∈ S then -a i else 0)

def rowTightFaceBounds
    (b : Fin n → ℝ) (S : Finset (Fin n)) : Fin (n + n) → ℝ :=
  Fin.append b (fun i => if i ∈ S then -b i else 0)

lemma hpoly_rowTightFace_eq
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (S : Finset (Fin n)) :
    Hpoly (rowTightFaceNormals a S) (rowTightFaceBounds b S) =
      rowTightFace a b S := by
  classical
  ext x
  constructor
  · intro hx
    have hP : x ∈ Hpoly a b := by
      intro i
      have hi := hx (Fin.castAdd n i)
      simpa [rowTightFaceNormals, rowTightFaceBounds] using hi
    refine ⟨hP, ?_⟩
    intro i hiS
    have hrev := hx (Fin.natAdd n i)
    change ⟪(if i ∈ S then -a i else 0), x⟫ ≤
      (if i ∈ S then -b i else 0) at hrev
    have hle := hP i
    simp only [if_pos hiS, inner_neg_left] at hrev
    linarith
  · rintro ⟨hP, htight⟩ i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa [rowTightFaceNormals, rowTightFaceBounds] using hP j
    · intro j
      change ⟪(if j ∈ S then -a j else 0), x⟫ ≤
        (if j ∈ S then -b j else 0)
      by_cases hj : j ∈ S
      · have heq := htight j hj
        simp only [if_pos hj, inner_neg_left]
        linarith
      · simp [hj]

/-- Appending reverse/tautological rows cannot destroy injectivity because the
first row block is exactly the original presentation. -/
theorem rowMap_rowTightFaceNormals_injective
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (S : Finset (Fin n))
    (hinj : Function.Injective (HirschCircuit.rowMap a)) :
    Function.Injective (HirschCircuit.rowMap (rowTightFaceNormals a S)) := by
  intro x y hxy
  apply hinj
  funext i
  have hi := congrFun hxy (Fin.castAdd n i)
  simpa [HirschCircuit.rowMap, rowTightFaceNormals] using hi

/-- Every nonempty row-tight face of an injective H-polyhedron contains an
original parent vertex, even when the parent is unbounded. -/
theorem rowTightFace_has_parent_vertex_of_rowMap_injective
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (S : Finset (Fin n))
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (hne : (rowTightFace a b S).Nonempty) :
    ∃ v, v ∈ extremePoints ℝ (Hpoly a b) ∧ v ∈ rowTightFace a b S := by
  have hEq := hpoly_rowTightFace_eq a b S
  have hneAug :
      (Hpoly (rowTightFaceNormals a S) (rowTightFaceBounds b S)).Nonempty := by
    rw [hEq]
    exact hne
  have hinjAug := rowMap_rowTightFaceNormals_injective a S hinj
  obtain ⟨v, hv⟩ := hpoly_extremePoints_nonempty_of_rowMap_injective
    (rowTightFaceNormals a S) (rowTightFaceBounds b S) hneAug hinjAug
  have hvFace : v ∈ extremePoints ℝ (rowTightFace a b S) := by
    rw [← hEq]
    exact hv
  have hFaceExtreme : IsExtreme ℝ (Hpoly a b) (rowTightFace a b S) := by
    refine ⟨fun _ hx => hx.1, ?_⟩
    intro p hp q hq z hz hopen
    refine ⟨hp, ?_⟩
    intro i hiS
    have hztight := hz.2 i hiS
    have hp_le := hp i
    have hq_le := hq i
    obtain ⟨α, β, hα, hβ, hαβ, hzcomb⟩ := hopen
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
  exact ⟨v, hFaceExtreme.extremePoints_subset_extremePoints hvFace, hvFace.1⟩

/-- A nonempty common carrier in an injective H-polyhedron contains a parent
vertex; compactness is unnecessary. -/
theorem commonFace_has_parent_vertex_of_rowMap_injective
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x z : EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (hz : z ∈ HirschPolynomialAccess.commonFace a b u x) :
    ∃ v, v ∈ extremePoints ℝ (Hpoly a b) ∧
      v ∈ HirschPolynomialAccess.commonFace a b u x := by
  let S := HirschPolynomialAccess.commonSourceRows a b u x
  have hEq : rowTightFace a b S = HirschPolynomialAccess.commonFace a b u x := by
    ext y
    rfl
  have hne : (rowTightFace a b S).Nonempty := by
    rw [hEq]
    exact ⟨z, hz⟩
  obtain ⟨v, hvP, hvF⟩ :=
    rowTightFace_has_parent_vertex_of_rowMap_injective a b S hinj hne
  exact ⟨v, hvP, by simpa [hEq] using hvF⟩

/-- Two common carriers meeting at a feasible checkpoint share a genuine parent
vertex in an injective H-polyhedron.  This is the noncompact portal needed to
connect consecutive circuit-carrier regions. -/
theorem commonFaces_shared_parent_vertex_of_rowMap_injective
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x p q z : EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (hz1 : z ∈ HirschPolynomialAccess.commonFace a b u x)
    (hz2 : z ∈ HirschPolynomialAccess.commonFace a b p q) :
    ∃ v, v ∈ extremePoints ℝ (Hpoly a b) ∧
      v ∈ HirschPolynomialAccess.commonFace a b u x ∧
      v ∈ HirschPolynomialAccess.commonFace a b p q := by
  let S := HirschPolynomialAccess.commonSourceRows a b u x ∪
    HirschPolynomialAccess.commonSourceRows a b p q
  have hzF : z ∈ rowTightFace a b S := by
    refine ⟨hz1.1, ?_⟩
    intro i hi
    rcases Finset.mem_union.1 hi with hi1 | hi2
    · exact hz1.2 i hi1
    · exact hz2.2 i hi2
  obtain ⟨v, hvP, hvF⟩ :=
    rowTightFace_has_parent_vertex_of_rowMap_injective a b S hinj ⟨z, hzF⟩
  refine ⟨v, hvP, ?_, ?_⟩
  · refine ⟨hvF.1, ?_⟩
    intro i hi
    exact hvF.2 i (Finset.mem_union_left _ hi)
  · refine ⟨hvF.1, ?_⟩
    intro i hi
    exact hvF.2 i (Finset.mem_union_right _ hi)

#print axioms hpoly_rowTightFace_eq
#print axioms rowMap_rowTightFaceNormals_injective
#print axioms rowTightFace_has_parent_vertex_of_rowMap_injective
#print axioms commonFace_has_parent_vertex_of_rowMap_injective
#print axioms commonFaces_shared_parent_vertex_of_rowMap_injective

end HirschPointed
