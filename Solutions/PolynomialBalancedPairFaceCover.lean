import Mathlib
import Solutions.PolynomialBalancedRowFaceCover

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 5000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschBalancedFaceCover

/-- Inside row face `i`, intersect with a distinct nonzero row face `j`.
The diagonal is replaced by the empty face so the family can still be indexed
by all rows. -/
def nonzeroRowPairFace {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (i j : Fin n) : Set (EuclideanSpace ℝ (Fin d)) :=
  if j = i then ∅ else nonzeroRowFace a b i ∩ nonzeroRowFace a b j

/-- Pair faces are extreme subsets of the first row face. -/
lemma nonzeroRowPairFace_isExtreme {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (i j : Fin n) :
    IsExtreme ℝ (nonzeroRowFace a b i) (nonzeroRowPairFace a b i j) := by
  classical
  by_cases hji : j = i
  · rw [nonzeroRowPairFace, if_pos hji]
    refine ⟨by simp, ?_⟩
    intro p hp q hq z hz hzopen
    exact False.elim hz
  · rw [nonzeroRowPairFace, if_neg hji]
    exact ((nonzeroRowFace_isExtreme a b i).inter
      (nonzeroRowFace_isExtreme a b j)).mono
      (nonzeroRowFace_isExtreme a b i).subset inter_subset_left

/-- Every extreme vertex of a nonzero row face lies on at least `d-1`
additional nonzero row faces. This is the second-level incidence multiplicity
behind iterated face averaging. -/
lemma row_face_vertex_pair_multiplicity {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (i : Fin n) (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (nonzeroRowFace a b i)) :
    d - 1 ≤
      (Finset.univ.filter (fun j => x ∈ nonzeroRowPairFace a b i j)).card := by
  classical
  have hxP : x ∈ extremePoints ℝ (Hpoly a b) :=
    (nonzeroRowFace_isExtreme a b i).extremePoints_subset_extremePoints hx
  have hglobal := vertex_nonzero_row_face_multiplicity a b x hxP
  let S : Finset (Fin n) :=
    Finset.univ.filter (fun j => x ∈ nonzeroRowFace a b j)
  have hiS : i ∈ S := by
    simp [S, hx.1]
  have hpairs :
      Finset.univ.filter (fun j => x ∈ nonzeroRowPairFace a b i j) = S.erase i := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [nonzeroRowPairFace, S]
    · simp [nonzeroRowPairFace, S, hji, hx.1]
  have hcard : (S.erase i).card + 1 = S.card := by
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨i, hiS⟩
    rw [Finset.card_erase_of_mem hiS]
    omega
  rw [hpairs]
  have hS : d ≤ S.card := by simpa [S] using hglobal
  omega

/-- Apply the shortest-path incidence bound one level inside a row face.
For `d ≥ 2`, intrinsic pair-face budgets are averaged with denominator `d-1`.
No assumption that shortest paths remain in a single subface is used. -/
theorem row_face_diamLE_of_pair_face_bounds {d n : ℕ}
    (hd : 1 < d)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (i : Fin n) (B : Fin n → ℕ)
    (hFD : ∀ j, DiamLE (nonzeroRowPairFace a b i j) (B j))
    (hconnect : ∀ u ∈ extremePoints ℝ (nonzeroRowFace a b i),
      ∀ v ∈ extremePoints ℝ (nonzeroRowFace a b i),
        ∃ L, HirschFaceSplice.Walk (nonzeroRowFace a b i) L u v) :
    DiamLE (nonzeroRowFace a b i)
      ((∑ j, (B j + 1)) / (d - 1) - 1) := by
  apply HirschFaceSplice.diamLE_of_face_cover
    d (d - 1) (by omega) (nonzeroRowFace a b i)
    (nonzeroRowPairFace a b i) B
    (nonzeroRowPairFace_isExtreme a b i) hFD
  · intro x hx
    exact row_face_vertex_pair_multiplicity a b i x hx
  · exact hconnect

#print axioms nonzeroRowPairFace_isExtreme
#print axioms row_face_vertex_pair_multiplicity
#print axioms row_face_diamLE_of_pair_face_bounds

end HirschBalancedFaceCover
