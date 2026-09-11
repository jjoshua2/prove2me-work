import Mathlib
import Solutions.PolynomialOneRowDeletionHorizonBridge

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschDeletion

/-- Reinsert the single deleted row by the generic finite clipping vocabulary. -/
theorem deletionOuter_singleCut_eq_parent
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (j : Fin n) :
    HirschRadial.clipSet (deletionOuter a b j)
        (fun _ : Fin 1 => a j) (fun _ : Fin 1 => b j) = Hpoly a b := by
  ext x
  constructor
  · intro hx i
    by_cases hij : i = j
    · subst i
      exact hx.2 0
    · exact hx.1 i hij
  · intro hx
    refine ⟨?_, ?_⟩
    · intro i hij
      exact hx i
    · intro _
      exact hx j

/-- With a strictly feasible centre for the deleted row, every point of the
deletion outer lying on or beyond a far cap retracts directly into the deleted
row facet of the original parent.  Because there is only one final cut, the
generic horizon theorem's existential active-face choice is forced to be that
same deleted row. -/
theorem deletion_horizon_retract_deletedRow_face
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (j : Fin n)
    (o : EuclideanSpace ℝ (Fin d))
    (ho : o ∈ deletionOuter a b j)
    (hstrict : ⟪a j, o⟫ < b j)
    (M : ℝ)
    (hsep : ∀ z ∈ Hpoly a b, deletionCapValue a j z < M)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ deletionOuter a b j)
    (hheight : M ≤ deletionCapValue a j x) :
    HirschRadial.retract (fun _ : Fin 1 => a j) (fun _ : Fin 1 => b j) o x ∈
      Hpoly a b ∩ {z | ⟪a j, z⟫ = b j} := by
  have hstrict' : ∀ i : Fin 1, ⟪(fun _ : Fin 1 => a j) i, o⟫ <
      (fun _ : Fin 1 => b j) i := by
    intro i
    exact hstrict
  have hsep' : ∀ z ∈ HirschRadial.clipSet (deletionOuter a b j)
      (fun _ : Fin 1 => a j) (fun _ : Fin 1 => b j),
      ⟪deletionCapNormal a j, z⟫ < M := by
    intro z hz
    rw [deletionCapNormal_inner]
    apply hsep z
    rw [← deletionOuter_singleCut_eq_parent a b j]
    exact hz
  have hheight' : M ≤ ⟪deletionCapNormal a j, x⟫ := by
    rw [deletionCapNormal_inner]
    exact hheight
  obtain ⟨i, hi⟩ :=
    HirschHorizon.horizon_retract_final_face
      (deletionOuter a b j) (deletionOuter_convex a b j)
      (fun _ : Fin 1 => a j) (fun _ : Fin 1 => b j)
      o ho hstrict' (deletionCapNormal a j) M hsep' x hx hheight'
  constructor
  · rw [← deletionOuter_singleCut_eq_parent a b j]
    exact hi.1
  · have hi0 : i = 0 := Subsingleton.elim _ _
    simpa [hi0] using hi.2

/-- The radial image of every segment contained in the cap horizon is contained
in the same deleted-row facet of the original parent.  This is the one-cut
specialization of `HirschHorizon.horizon_chord_shadow`. -/
theorem deletion_horizon_chord_shadow_deletedRow_face
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (j : Fin n)
    (o : EuclideanSpace ℝ (Fin d))
    (ho : o ∈ deletionOuter a b j)
    (hstrict : ⟪a j, o⟫ < b j)
    (M : ℝ)
    (hsep : ∀ z ∈ Hpoly a b, deletionCapValue a j z < M)
    (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ deletionOuter a b j) (hy : y ∈ deletionOuter a b j)
    (hxc : deletionCapValue a j x = M)
    (hyc : deletionCapValue a j y = M) :
    ∀ z ∈ segment ℝ x y,
      HirschRadial.retract (fun _ : Fin 1 => a j) (fun _ : Fin 1 => b j) o z ∈
        Hpoly a b ∩ {p | ⟪a j, p⟫ = b j} := by
  have hstrict' : ∀ i : Fin 1, ⟪(fun _ : Fin 1 => a j) i, o⟫ <
      (fun _ : Fin 1 => b j) i := by
    intro i
    exact hstrict
  have hsep' : ∀ z ∈ HirschRadial.clipSet (deletionOuter a b j)
      (fun _ : Fin 1 => a j) (fun _ : Fin 1 => b j),
      ⟪deletionCapNormal a j, z⟫ < M := by
    intro z hz
    rw [deletionCapNormal_inner]
    apply hsep z
    rw [← deletionOuter_singleCut_eq_parent a b j]
    exact hz
  have hxc' : ⟪deletionCapNormal a j, x⟫ = M := by
    rw [deletionCapNormal_inner]
    exact hxc
  have hyc' : ⟪deletionCapNormal a j, y⟫ = M := by
    rw [deletionCapNormal_inner]
    exact hyc
  intro z hz
  obtain ⟨i, hi⟩ :=
    HirschHorizon.horizon_chord_shadow
      (deletionOuter a b j) (deletionOuter_convex a b j)
      (fun _ : Fin 1 => a j) (fun _ : Fin 1 => b j)
      o ho hstrict' (deletionCapNormal a j) M hsep'
      x y hx hy hxc' hyc' z hz
  constructor
  · rw [← deletionOuter_singleCut_eq_parent a b j]
    exact hi.1
  · have hi0 : i = 0 := Subsingleton.elim _ _
    simpa [hi0] using hi.2

#print axioms deletionOuter_singleCut_eq_parent
#print axioms deletion_horizon_retract_deletedRow_face
#print axioms deletion_horizon_chord_shadow_deletedRow_face

end HirschDeletion
