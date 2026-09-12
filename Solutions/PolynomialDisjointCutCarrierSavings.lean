import Mathlib
import Solutions.PolynomialFacePreservingCheckpoints
import Solutions.PolynomialCommonFaceStrictRowSavings

/-!
# Disjoint cut faces force strict rows on portal-pair carriers

PR #186 proves that ambient rows which are strictly slack throughout a common
carrier reduce that carrier's minimum-presentation excess.  This module supplies
the geometric bridge needed by the used-region path argument.

For an H-polyhedron, the row face for row `i` is the parent intersected with the
supporting equality `a_i x = b_i`.  If two closed extreme parent faces have no
shared parent extreme vertex, compactness forces them to be disjoint: any
ordinary intersection point would produce such a vertex portal by the existing
face-preserving checkpoint theorem.

If a portal pair `p,q` is tight on row `i`, its common carrier lies in row face
`i`.  Therefore any row face disjoint from row face `i` is strictly slack at
every point of that carrier.  Feeding a whole finite family of such rows into
PR #186 yields a quantitative excess saving.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess HirschRegionRoute

/-- The parent face cut out by equality in one describing row. -/
def hpolyRowFace {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (i : Fin n) : Set (EuclideanSpace ℝ (Fin d)) :=
  Hpoly a b ∩ {x | ⟪a i, x⟫ = b i}

/-- A row which is tight somewhere and strictly slack somewhere else cannot
have zero normal.  This is the form naturally supplied by a used target-slack
cut: its portal lies on the row face while the fixed target is strictly inside. -/
theorem row_ne_zero_of_tight_and_strict
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (i : Fin n) (p v : EuclideanSpace ℝ (Fin d))
    (hp : ⟪a i, p⟫ = b i) (hv : ⟪a i, v⟫ < b i) :
    a i ≠ 0 := by
  intro hai
  rw [hai, inner_zero_left] at hp hv
  linarith

/-- If two closed extreme faces of a compact parent had any common point, the
existing portal theorem would produce a shared parent extreme vertex.  Hence
absence of such a parent-vertex portal implies actual set disjointness. -/
theorem closed_extreme_faces_disjoint_of_no_parent_vertex_portal
    {d : ℕ}
    (P F G : Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P)
    (hF : IsExtreme ℝ P F) (hG : IsExtreme ℝ P G)
    (hFc : IsClosed F) (hGc : IsClosed G)
    (hno : ¬ ∃ v : EuclideanSpace ℝ (Fin d),
      v ∈ extremePoints ℝ P ∧ v ∈ F ∧ v ∈ G) :
    Disjoint F G := by
  rw [Set.disjoint_left]
  intro x hxF hxG
  obtain ⟨v, hv, hvF, hvG⟩ :=
    compact_faces_shared_point_portal P F G hP hF hG hFc hGc x hxF hxG
  exact hno ⟨v, hv, hvF, hvG⟩

/-- Nonadjacency in the parent-vertex region graph of closed extreme faces means
the underlying faces are genuinely disjoint (provided the labels are distinct).
This is the exact bridge consumed by a chordless used-region path. -/
theorem closed_extreme_faces_disjoint_of_region_nonadj
    {d : ℕ} {ι : Type*}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i))
    {i j : ι} (hij : i ≠ j)
    (hnadj : ¬
      (intersectionGraph (fun k => extremePoints ℝ P ∩ F k)).Adj i j) :
    Disjoint (F i) (F j) := by
  apply closed_extreme_faces_disjoint_of_no_parent_vertex_portal
    P (F i) (F j) hP (hF i) (hF j) (hclosed i) (hclosed j)
  rintro ⟨v, hv, hvi, hvj⟩
  apply hnadj
  exact ⟨hij, v, ⟨hv, hvi⟩, ⟨hv, hvj⟩⟩

/-- If a nonzero row is tight at both portal vertices, their whole common
carrier lies in that row face. -/
theorem commonFace_subset_hpolyRowFace_of_tight
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (p q : EuclideanSpace ℝ (Fin d)) (i : Fin n)
    (hai : a i ≠ 0)
    (hpi : ⟪a i, p⟫ = b i) (hqi : ⟪a i, q⟫ = b i) :
    commonFace a b p q ⊆ hpolyRowFace a b i := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  apply hz.2 i
  simp [commonSourceRows, hai, hpi, hqi]

/-- A row face disjoint from the face containing a portal-pair carrier is
strictly slack at every point of that carrier.  Endpoint slackness alone would
not suffice; the set-disjointness hypothesis is what gives strictness on the
entire carrier. -/
theorem row_strict_on_commonFace_of_disjoint_rowFaces
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (p q : EuclideanSpace ℝ (Fin d)) (i j : Fin n)
    (hai : a i ≠ 0)
    (hpi : ⟪a i, p⟫ = b i) (hqi : ⟪a i, q⟫ = b i)
    (hdisj : Disjoint (hpolyRowFace a b i) (hpolyRowFace a b j)) :
    ∀ z ∈ commonFace a b p q, ⟪a j, z⟫ < b j := by
  intro z hz
  have hzi : z ∈ hpolyRowFace a b i :=
    commonFace_subset_hpolyRowFace_of_tight a b p q i hai hpi hqi hz
  have hne : ⟪a j, z⟫ ≠ b j := by
    intro hzjEq
    have hzj : z ∈ hpolyRowFace a b j := ⟨hz.1, hzjEq⟩
    exact (Set.disjoint_left.1 hdisj) hzi hzj
  exact lt_of_le_of_ne (hz.1 j) hne

/-- Quantitative bridge from a family of disjoint cut faces to the PR #186
minimum-presentation-excess saving.

Every row in `J` has a row face disjoint from the current row face `i`; hence it
is strict throughout the actual portal-pair common carrier on `i`. -/
theorem commonFace_minExcess_add_disjoint_rowFaces_le
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (p q : EuclideanSpace ℝ (Fin d))
    (hp : p ∈ extremePoints ℝ (Hpoly a b))
    (hq : q ∈ extremePoints ℝ (Hpoly a b))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (i : Fin n) (hai : a i ≠ 0)
    (hpi : ⟪a i, p⟫ = b i) (hqi : ⟪a i, q⟫ = b i)
    (J : Finset (Fin n))
    (hJ : ∀ j, j ∈ J →
      Disjoint (hpolyRowFace a b i) (hpolyRowFace a b j)) :
    (commonFaceMinSubpresentationCount a b p q - commonFaceDim a b p q) +
        J.card ≤ n - d := by
  apply commonFace_minExcess_add_strictRows_le
    a b p q hbd hp hq J
  intro j hj z hz
  exact row_strict_on_commonFace_of_disjoint_rowFaces
    a b p q i j hai hpi hqi (hJ j hj) z hz

/-- Target-slack specialization: tightness at a used cut portal and strictness at
the fixed target automatically prove that the current cut row is nonzero. -/
theorem commonFace_minExcess_add_disjoint_targetSlack_rowFaces_le
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (target p q : EuclideanSpace ℝ (Fin d))
    (hp : p ∈ extremePoints ℝ (Hpoly a b))
    (hq : q ∈ extremePoints ℝ (Hpoly a b))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (i : Fin n)
    (htarget : ⟪a i, target⟫ < b i)
    (hpi : ⟪a i, p⟫ = b i) (hqi : ⟪a i, q⟫ = b i)
    (J : Finset (Fin n))
    (hJ : ∀ j, j ∈ J →
      Disjoint (hpolyRowFace a b i) (hpolyRowFace a b j)) :
    (commonFaceMinSubpresentationCount a b p q - commonFaceDim a b p q) +
        J.card ≤ n - d := by
  exact commonFace_minExcess_add_disjoint_rowFaces_le
    a b p q hp hq hbd i
    (row_ne_zero_of_tight_and_strict a b i p target hpi htarget)
    hpi hqi J hJ

#print axioms row_ne_zero_of_tight_and_strict
#print axioms closed_extreme_faces_disjoint_of_no_parent_vertex_portal
#print axioms closed_extreme_faces_disjoint_of_region_nonadj
#print axioms commonFace_subset_hpolyRowFace_of_tight
#print axioms row_strict_on_commonFace_of_disjoint_rowFaces
#print axioms commonFace_minExcess_add_disjoint_rowFaces_le
#print axioms commonFace_minExcess_add_disjoint_targetSlack_rowFaces_le

end HirschCircuitLocalization
