import Solutions.PolynomialCompactCapVertexClassification
import Solutions.PolynomialOneRowDeletionFarCapLevel

/-!
Candidate integration of the compact-cap vertex classification with the explicit
one-row-deletion cap. NOT yet kernel-verified; no Prove2Me status is claimed.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschDeletion

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
namespace HirschCapVertices

variable {d n : ℕ}

def deletionOuterSet
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (j : Fin n) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, i ≠ j → ⟪a i, x⟫ ≤ b i}

def erasedNormals (a : Fin n → EuclideanSpace ℝ (Fin d)) (j : Fin n) :
    Fin n → EuclideanSpace ℝ (Fin d) := fun i => if i = j then 0 else a i

def erasedBounds (b : Fin n → ℝ) (j : Fin n) : Fin n → ℝ :=
  fun i => if i = j then 0 else b i

def deletionCapNormal (a : Fin n → EuclideanSpace ℝ (Fin d)) (j : Fin n) :
    EuclideanSpace ℝ (Fin d) := - ∑ i : {i : Fin n // i ≠ j}, a i.1

lemma erased_hpoly_eq_deletionOuterSet
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (j : Fin n) :
    Hpoly (erasedNormals a j) (erasedBounds b j) = deletionOuterSet a b j := by
  classical
  ext x
  constructor
  · intro hx i hij
    have h := hx i
    simpa [erasedNormals, erasedBounds, hij] using h
  · intro hx i
    by_cases hij : i = j
    · simp [erasedNormals, erasedBounds, hij]
    · simpa [erasedNormals, erasedBounds, hij] using hx i hij

lemma deletionCapNormal_eval
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (j : Fin n)
    (x : EuclideanSpace ℝ (Fin d)) :
    ⟪deletionCapNormal a j, x⟫ = deletionCapValue a j x := by
  classical
  simp [deletionCapNormal, deletionCapValue, sum_inner, Finset.sum_neg_distrib]

lemma deletionOuterSet_cap_eq
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (j : Fin n) (M : ℝ) :
    deletionOuterSet a b j ∩ {x | ⟪deletionCapNormal a j, x⟫ ≤ M} =
      deletionCappedOuter a b j M := by
  ext x
  change ((∀ i, i ≠ j → ⟪a i, x⟫ ≤ b i) ∧ ⟪deletionCapNormal a j, x⟫ ≤ M) ↔
    ((∀ i, i ≠ j → ⟪a i, x⟫ ≤ b i) ∧ deletionCapValue a j x ≤ M)
  rw [deletionCapNormal_eval]

/-- Full geometric witness for an explicit one-row-deletion far cap:
compactness, strict separation from the entire parent and ALL outer vertices,
exact recovery, preservation of old vertices/edges, and new-vertex adjacency.

The zeroed row is only a convenient finite encoding for vertex classification;
it is NOT used to claim a row-count/excess saving. No graph-diameter bound for
the unbounded deletion outer or the final blocker face is assumed or proved.
-/
theorem exists_deletion_cap_with_vertex_classification
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b)) (hne : (Hpoly a b).Nonempty)
    (j : Fin n) :
    ∃ M : ℝ,
      IsCompact (deletionCappedOuter a b j M) ∧
      (∀ x ∈ Hpoly a b, deletionCapValue a j x < M) ∧
      (∀ x ∈ extremePoints ℝ (deletionOuterSet a b j), deletionCapValue a j x < M) ∧
      (deletionCappedOuter a b j M ∩ {x | ⟪a j, x⟫ ≤ b j} = Hpoly a b) ∧
      (∀ x ∈ extremePoints ℝ (deletionOuterSet a b j),
        x ∈ extremePoints ℝ (deletionCappedOuter a b j M)) ∧
      (∀ u v, Adj (deletionOuterSet a b j) u v → Adj (deletionCappedOuter a b j M) u v) ∧
      (∀ z ∈ extremePoints ℝ (deletionCappedOuter a b j M),
        z ∈ extremePoints ℝ (deletionOuterSet a b j) ∨
          (deletionCapValue a j z = M ∧
            ∃ v ∈ extremePoints ℝ (deletionOuterSet a b j),
              deletionCapValue a j v < M ∧ Adj (deletionCappedOuter a b j M) v z)) := by
  classical
  let Q := deletionOuterSet a b j
  let c := deletionCapNormal a j
  have hQmodel : Hpoly (erasedNormals a j) (erasedBounds b j) = Q :=
    erased_hpoly_eq_deletionOuterSet a b j
  have hPc : IsCompact (Hpoly a b) :=
    Metric.isCompact_iff_isClosed_bounded.2 ⟨hpoly_isClosed a b, hbd⟩
  obtain ⟨M, hPbelow, hVbelow⟩ := exists_level_above_compact_and_outer_vertices
    (erasedNormals a j) (erasedBounds b j) (Hpoly a b) hPc hne c
  rw [hQmodel] at hVbelow
  let R := deletionCappedOuter a b j M
  have hRmodel : Q ∩ {x | ⟪c, x⟫ ≤ M} = R := deletionOuterSet_cap_eq a b j M
  have hQc : IsClosed Q := by
    rw [← hQmodel]
    exact hpoly_isClosed _ _
  have hRc : IsCompact R := by
    have hclosed : IsClosed R := by
      rw [← hRmodel]
      exact hQc.inter (isClosed_le (by fun_prop) continuous_const)
    obtain ⟨x, hx⟩ := hne
    have hbounded : Bornology.IsBounded R :=
      deletionCappedOuter_isBounded_of_bounded_parent a b hbd x hx j M
    exact Metric.isCompact_iff_isClosed_bounded.2 ⟨hclosed, hbounded⟩
  have hPval : ∀ x ∈ Hpoly a b, deletionCapValue a j x < M := by
    intro x hx
    simpa only [c, deletionCapNormal_eval] using hPbelow x hx
  have hVval : ∀ x ∈ extremePoints ℝ Q, deletionCapValue a j x < M := by
    intro x hx
    simpa only [c, deletionCapNormal_eval] using hVbelow x hx
  have hcontain : ∀ x ∈ Hpoly a b, x ∈ deletionCappedOuter a b j M := by
    intro x hx
    exact ⟨fun i _ => hx i, (hPval x hx).le⟩
  refine ⟨M, hRc, hPval, hVval,
    deletionCappedOuter_inter_deletedRow_eq_parent a b j M hcontain, ?_, ?_, ?_⟩
  · intro x hx
    change x ∈ extremePoints ℝ R
    rw [← hRmodel]
    exact old_vertex_survives_cap Q c M x hx (hVbelow x hx).le
  · intro u v huv
    change Adj R u v
    rw [← hRmodel]
    exact old_edge_survives_cap Q c M u v huv
      (hVbelow u (HirschPolynomialAccess.adj_left_extreme Q huv)).le
      (hVbelow v (HirschPolynomialAccess.adj_right_extreme Q huv)).le
  · intro z hz
    have hcomp : IsCompact (Hpoly (erasedNormals a j) (erasedBounds b j) ∩
        {x | ⟪c, x⟫ ≤ M}) := by
      simpa only [hQmodel, hRmodel] using hRc
    have hz' : z ∈ extremePoints ℝ (Hpoly (erasedNormals a j) (erasedBounds b j) ∩
        {x | ⟪c, x⟫ ≤ M}) := by
      simpa only [hQmodel, hRmodel] using hz
    have hclass := compact_hpoly_cap_vertex_classification
      (erasedNormals a j) (erasedBounds b j) c M hcomp z hz'
    simpa only [hQmodel, hRmodel, c, deletionCapNormal_eval] using hclass

#print axioms erased_hpoly_eq_deletionOuterSet
#print axioms deletionCapNormal_eval
#print axioms deletionOuterSet_cap_eq
#print axioms exists_deletion_cap_with_vertex_classification

end HirschCapVertices
