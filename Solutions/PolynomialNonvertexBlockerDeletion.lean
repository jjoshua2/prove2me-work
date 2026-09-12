import Mathlib
import Solutions.PolynomialCircuitSupportDeletionPointedness
import Solutions.PolynomialCircuitStepProgress
import Solutions.PolynomialFaceReentrySplice

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- If every row except `j` annihilates a nonzero direction `g`, then every
vertex of the H-polyhedron is tight on row `j`.

No boundedness, circuit, irredundancy, or injectivity hypothesis is needed.  If
some vertex were slack on `j`, every row tight at that vertex would annihilate
`g`; the checked vertex active-row spanning theorem would force `g = 0`. -/
theorem vertices_tight_on_unique_nonneutral_row
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (g : EuclideanSpace ℝ (Fin d)) (hg : g ≠ 0)
    (j : Fin n)
    (hneutral : ∀ i : Fin n, i ≠ j → ⟪a i, g⟫ = 0) :
    ∀ z ∈ extremePoints ℝ (Hpoly a b), ⟪a j, z⟫ = b j := by
  intro z hz
  by_contra hjz
  have htight : ∀ i : Fin n, ⟪a i, z⟫ = b i → ⟪a i, g⟫ = 0 := by
    intro i hi
    by_cases hij : i = j
    · subst i
      exact False.elim (hjz hi)
    · exact hneutral i hij
  exact hg (HirschPolynomialAccess.vertex_tight_rows_span_checked
    d n a b z hz g htight)

/-- For a maximal nonstationary circuit step in an injective finite
H-presentation, choose a destination-tight increasing blocker `j`.  Then either
removing `j` preserves row-map injectivity, or every original parent vertex is
tight on `j`.

This removes the source-vertex hypothesis from the row-deletion alternative in
#158 while exposing the exact exceptional case instead of assuming deletion is
always pointed. -/
theorem rowCircuitStep_target_blocker_pointed_delete_or_all_vertices_tight
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (x y : EuclideanSpace ℝ (Fin d))
    (hstep : RowCircuitStep a b x y) :
    ∃ j : Fin n,
      a j ≠ 0 ∧
      ⟪a j, y⟫ = b j ∧
      0 < ⟪a j, y - x⟫ ∧
      (Function.Injective (HirschCircuit.rowMap (HirschDeletion.rowsWithout a j)) ∨
        ∀ z ∈ extremePoints ℝ (Hpoly a b), ⟪a j, z⟫ = b j) := by
  classical
  obtain ⟨j, hja, hjy, hjpos⟩ :=
    rowCircuitStep_exists_target_blocking_row a b x y hstep
  let g := y - x
  by_cases hother : ∃ i : Fin n, i ≠ j ∧ ⟪a i, g⟫ ≠ 0
  · obtain ⟨i, hij, hi⟩ := hother
    refine ⟨j, hja, hjy, hjpos, Or.inl ?_⟩
    exact HirschDeletion.rowMap_rowsWithout_injective_of_two_nonneutral_rowCircuit
      a hinj g hstep.2.2.1 i j hi (ne_of_gt hjpos) hij
  · have hneutral : ∀ i : Fin n, i ≠ j → ⟪a i, g⟫ = 0 := by
      intro i hij
      by_contra hi
      exact hother ⟨i, hij, hi⟩
    refine ⟨j, hja, hjy, hjpos, Or.inr ?_⟩
    exact vertices_tight_on_unique_nonneutral_row
      a b g hstep.2.2.1.1 j hneutral

/-- If every parent vertex lies in one extreme face, any intrinsic graph budget
for that face is already a graph budget for the whole parent. -/
theorem diamLE_of_all_vertices_in_extreme_face
    {d B : ℕ}
    (P F : Set (EuclideanSpace ℝ (Fin d)))
    (hF : IsExtreme ℝ P F)
    (hall : ∀ z ∈ extremePoints ℝ P, z ∈ F)
    (hFD : DiamLE F B) :
    DiamLE P B := by
  intro u hu v hv
  have huF : u ∈ extremePoints ℝ F :=
    HirschFaceSplice.extreme_in_extreme_face hF hu (hall u hu)
  have hvF : v ∈ extremePoints ℝ F :=
    HirschFaceSplice.extreme_in_extreme_face hF hv (hall v hv)
  obtain ⟨w, hw0, hwB, hstep⟩ := hFD u huF v hvF
  refine ⟨w, hw0, hwB, ?_⟩
  intro k hk
  rcases hstep k hk with heq | hadj
  · exact Or.inl heq
  · exact Or.inr (HirschFaceSplice.face_adj_to_parent hF hadj)

/-- Cost-facing form of the nonvertex blocker dichotomy.  The exceptional
one-nonneutral-row case needs no deletion-outer budget: all parent vertices lie
in the blocker supporting face, so any graph budget for that face immediately
routes the parent.

The first branch records the genuinely pointed one-row deletion child and leaves
its graph cost to the recursive pointed interface. -/
theorem rowCircuitStep_target_blocker_pointed_delete_or_face_controls_parent
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (x y : EuclideanSpace ℝ (Fin d))
    (hstep : RowCircuitStep a b x y) :
    ∃ j : Fin n,
      a j ≠ 0 ∧
      ⟪a j, y⟫ = b j ∧
      0 < ⟪a j, y - x⟫ ∧
      (Function.Injective (HirschCircuit.rowMap (HirschDeletion.rowsWithout a j)) ∨
        ∀ B : ℕ,
          DiamLE ((Hpoly a b) ∩ {z | ⟪a j, z⟫ = b j}) B →
          DiamLE (Hpoly a b) B) := by
  obtain ⟨j, hja, hjy, hjpos, hcase⟩ :=
    rowCircuitStep_target_blocker_pointed_delete_or_all_vertices_tight
      a b hinj x y hstep
  refine ⟨j, hja, hjy, hjpos, ?_⟩
  rcases hcase with hdel | hall
  · exact Or.inl hdel
  · right
    intro B hface
    have hF : IsExtreme ℝ (Hpoly a b)
        ((Hpoly a b) ∩ {z | ⟪a j, z⟫ = b j}) :=
      HirschClipLift.supporting_equality_extreme
        (Hpoly a b) (a j) (b j) (fun z hz => hz j)
    exact diamLE_of_all_vertices_in_extreme_face
      (Hpoly a b) ((Hpoly a b) ∩ {z | ⟪a j, z⟫ = b j})
      hF (fun z hz => ⟨hz.1, hall z hz⟩) hface

#print axioms vertices_tight_on_unique_nonneutral_row
#print axioms rowCircuitStep_target_blocker_pointed_delete_or_all_vertices_tight
#print axioms diamLE_of_all_vertices_in_extreme_face
#print axioms rowCircuitStep_target_blocker_pointed_delete_or_face_controls_parent

end HirschCircuitLocalization
