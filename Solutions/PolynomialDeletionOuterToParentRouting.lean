import Mathlib
import Definitions.Def_Hirsch_circuit_model
import Solutions.PolynomialCurrentExteriorCapParentFaceRoute
import Solutions.PolynomialOneRowDeletionCapWitness
import Solutions.PolynomialOneRowDeletionHorizonShadow

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 7000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschDeletionRouting

open HirschRegionRoute

variable {d n D B : ℕ}

private lemma deletionOuterSet_convex
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (j : Fin n) :
    Convex ℝ (HirschCapVertices.deletionOuterSet a b j) := by
  rw [← HirschCapVertices.erased_hpoly_eq_deletionOuterSet a b j]
  exact HirschCapVertices.hpoly_convex _ _

private lemma deletionOuterSet_eq_deletionOuter
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (j : Fin n) :
    HirschCapVertices.deletionOuterSet a b j = HirschDeletion.deletionOuter a b j := by
  rfl

private lemma deletionCappedOuter_eq_clipSet
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (j : Fin n) (M : ℝ) :
    HirschDeletion.deletionCappedOuter a b j M =
      HirschRadial.clipSet (HirschCapVertices.deletionOuterSet a b j)
        (fun _ : Fin 1 => HirschCapVertices.deletionCapNormal a j)
        (fun _ : Fin 1 => M) := by
  ext x
  simp only [HirschRadial.clipSet, Set.mem_inter_iff, Set.mem_setOf_eq]
  change
    ((∀ i : Fin n, i ≠ j → ⟪a i, x⟫ ≤ b i) ∧
      HirschDeletion.deletionCapValue a j x ≤ M) ↔
    ((∀ i : Fin n, i ≠ j → ⟪a i, x⟫ ≤ b i) ∧
      ∀ _ : Fin 1, ⟪HirschCapVertices.deletionCapNormal a j, x⟫ ≤ M)
  constructor
  · rintro ⟨hout, hcap⟩
    refine ⟨hout, ?_⟩
    intro k
    rw [HirschCapVertices.deletionCapNormal_eval]
    exact hcap
  · rintro ⟨hout, hcap⟩
    refine ⟨hout, ?_⟩
    have h := hcap 0
    rw [HirschCapVertices.deletionCapNormal_eval] at h
    exact h

/-- Reinsert one deleted row after routing the pointed deletion outer.

The outer graph budget `D` may come from an unbounded pointed H-polyhedron.  A
far explicit cap is used only as a compact proof device: #147 preserves every
old outer vertex and edge and attaches each new cap vertex by one genuine edge.
The horizon-shadow theorem sends every cap shortcut into the deleted-row face;
#152 repairs those shortcuts using the supplied ambient parent-face route budget
`B`.  Thus the final parent costs `D + 1 + B`.

No polynomial claim about `D` or `B` is made by this theorem. -/
theorem hpoly_diamLE_of_deletionOuter_diam_and_parent_face_route
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (j : Fin n)
    (o : EuclideanSpace ℝ (Fin d))
    (hoP : o ∈ Hpoly a b)
    (hostrict : ⟪a j, o⟫ < b j)
    (hOld : DiamLE (HirschCapVertices.deletionOuterSet a b j) D)
    (hFaceRoute :
      ∀ u ∈ extremePoints ℝ (Hpoly a b), ⟪a j, u⟫ = b j →
      ∀ v ∈ extremePoints ℝ (Hpoly a b), ⟪a j, v⟫ = b j →
        Route (Adj (Hpoly a b)) B u v) :
    DiamLE (Hpoly a b) (D + 1 + B) := by
  classical
  obtain ⟨M, hRc, hPbelow, hVbelow, hrecover, hVsurvive, hEsurvive, hclass0⟩ :=
    HirschCapVertices.exists_deletion_cap_with_vertex_classification
      a b hbd ⟨o, hoP⟩ j
  let O := HirschCapVertices.deletionOuterSet a b j
  let R := HirschDeletion.deletionCappedOuter a b j M
  let G : Set (EuclideanSpace ℝ (Fin d)) :=
    R ∩ {x | HirschDeletion.deletionCapValue a j x = M}
  let V : Set (EuclideanSpace ℝ (Fin d)) := extremePoints ℝ O
  have hOconv : Convex ℝ O := by
    simpa [O] using deletionOuterSet_convex a b j
  have hRconv : Convex ℝ R := by
    change Convex ℝ (HirschDeletion.deletionCappedOuter a b j M)
    rw [deletionCappedOuter_eq_clipSet a b j M]
    exact HirschRadial.clipSet_convex _ (deletionOuterSet_convex a b j)
      (fun _ : Fin 1 => HirschCapVertices.deletionCapNormal a j)
      (fun _ : Fin 1 => M)
  have hoO : o ∈ O := by
    intro i hij
    exact hoP i
  have hoR : o ∈ R := by
    refine ⟨?_, (hPbelow o hoP).le⟩
    intro i hij
    exact hoP i
  have hOldR : ∀ x ∈ V, ∀ y ∈ V, Route (Adj R) D x y := by
    intro x hx y hy
    obtain ⟨w, hw0, hwD, hstep⟩ := hOld x hx y hy
    refine ⟨w, hw0, hwD, ?_⟩
    intro k hk
    rcases hstep k hk with heq | hedge
    · exact Or.inl heq
    · exact Or.inr (hEsurvive _ _ hedge)
  have hclass : ∀ x ∈ extremePoints ℝ R,
      x ∈ V ∨ (x ∈ G ∧ ∃ y ∈ V, Adj R y x) := by
    intro x hx
    rcases hclass0 x hx with hold | ⟨hcap, y, hyV, _hybelow, hyx⟩
    · exact Or.inl hold
    · exact Or.inr ⟨⟨hx.1, hcap⟩, y, hyV, hyx⟩
  have hfinal :
      HirschRadial.clipSet R (fun _ : Fin 1 => a j) (fun _ : Fin 1 => b j) =
        Hpoly a b := by
    simpa [R, HirschRadial.clipSet] using hrecover
  have hFaceRoute' :
      ∀ u ∈ extremePoints ℝ
          (HirschRadial.clipSet R (fun _ : Fin 1 => a j) (fun _ : Fin 1 => b j)),
        ⟪a j, u⟫ = b j →
      ∀ v ∈ extremePoints ℝ
          (HirschRadial.clipSet R (fun _ : Fin 1 => a j) (fun _ : Fin 1 => b j)),
        ⟪a j, v⟫ = b j →
        Route (Adj (HirschRadial.clipSet R (fun _ : Fin 1 => a j)
          (fun _ : Fin 1 => b j))) B u v := by
    intro u hu hut v hv hvt
    rw [hfinal] at hu hv ⊢
    exact hFaceRoute u hu hut v hv hvt
  have hShadow : ∀ x ∈ G, ∀ y ∈ G, ∀ z ∈ segment ℝ x y,
      HirschRadial.retract (fun _ : Fin 1 => a j) (fun _ : Fin 1 => b j) o z ∈
        HirschRadial.clipSet R (fun _ : Fin 1 => a j) (fun _ : Fin 1 => b j) ∩
          {p | ⟪a j, p⟫ = b j} := by
    intro x hx y hy z hz
    have hxO : x ∈ HirschDeletion.deletionOuter a b j := by
      rw [← deletionOuterSet_eq_deletionOuter a b j]
      exact hx.1.1
    have hyO : y ∈ HirschDeletion.deletionOuter a b j := by
      rw [← deletionOuterSet_eq_deletionOuter a b j]
      exact hy.1.1
    have hoO' : o ∈ HirschDeletion.deletionOuter a b j := by
      rw [← deletionOuterSet_eq_deletionOuter a b j]
      exact hoO
    have hs := HirschDeletion.deletion_horizon_chord_shadow_deletedRow_face
      a b j o hoO' hostrict M hPbelow x y hxO hyO hx.2 hy.2 z hz
    rw [hfinal]
    exact hs
  have hout :=
    HirschExteriorCurrent.diamLE_single_clip_of_old_routes_and_cap_classification_with_parent_face_route
      R G V hRc hRconv (a j) (b j) o hoR hostrict D B
      hOldR hclass hFaceRoute' hShadow
  rw [hfinal] at hout
  exact hout

/-- Convenience form for the strictly-feasible minimum carrier models used by
the row-excess recursion. -/
theorem hpoly_diamLE_of_deletionOuter_diam_and_parent_face_route_of_strictRows
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hstrictRows : StrictlyFeasibleRows a b)
    (j : Fin n)
    (hOld : DiamLE (HirschCapVertices.deletionOuterSet a b j) D)
    (hFaceRoute :
      ∀ u ∈ extremePoints ℝ (Hpoly a b), ⟪a j, u⟫ = b j →
      ∀ v ∈ extremePoints ℝ (Hpoly a b), ⟪a j, v⟫ = b j →
        Route (Adj (Hpoly a b)) B u v) :
    DiamLE (Hpoly a b) (D + 1 + B) := by
  obtain ⟨o, ho⟩ := hstrictRows
  have hoP : o ∈ Hpoly a b := fun i => (ho i).le
  exact hpoly_diamLE_of_deletionOuter_diam_and_parent_face_route
    a b hbd j o hoP (ho j) hOld hFaceRoute

#print axioms hpoly_diamLE_of_deletionOuter_diam_and_parent_face_route
#print axioms hpoly_diamLE_of_deletionOuter_diam_and_parent_face_route_of_strictRows

end HirschDeletionRouting
