import Mathlib
import Solutions.PolynomialCommonFaceCoords
import Solutions.PolynomialCircuitInjectiveNeutralRank

open scoped RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- Injectivity of the ambient row-evaluation map descends to the intrinsic
common-face coordinate presentation.  The coordinate model retains every
original row restricted to the common direction space, and the coordinate lift
is injective. -/
theorem rowMap_commonFaceA_injective_of_injective
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (HirschCircuit.rowMap a)) :
    Function.Injective
      (HirschCircuit.rowMap (commonFaceA a b u x)) := by
  intro p q hpq
  apply (commonFaceLift a b u x).injective
  apply hinj
  funext i
  have hi := congrFun hpq i
  change ⟪commonFaceA a b u x i, p⟫ =
      ⟪commonFaceA a b u x i, q⟫ at hi
  rw [commonFace_inner_restricted, commonFace_inner_restricted] at hi
  exact hi

/-- Pointedness/injectivity is a property of a nonempty H-polyhedron, not of a
particular equivalent finite presentation: every equivalent presentation of a
nonempty injective H-polyhedron has injective row map.

If a direction were annihilated by all rows of the second presentation, a
feasible point could be translated by every real multiple of that direction.
Equality of feasible sets would put the whole line in the first presentation;
choosing one multiple tailored to any nonzero first-row evaluation contradicts
that row inequality. -/
theorem rowMap_injective_of_equivalent_nonempty_hpoly
    {d n m : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (a' : Fin m → EuclideanSpace ℝ (Fin d)) (b' : Fin m → ℝ)
    (heq : Hpoly a' b' = Hpoly a b)
    (hne : (Hpoly a b).Nonempty)
    (hinj : Function.Injective (HirschCircuit.rowMap a)) :
    Function.Injective (HirschCircuit.rowMap a') := by
  intro p q hpq
  let g := p - q
  have hg' : ∀ j : Fin m, ⟪a' j, g⟫ = 0 := by
    intro j
    have hj := congrFun hpq j
    change ⟪a' j, p⟫ = ⟪a' j, q⟫ at hj
    dsimp [g]
    rw [inner_sub_right, hj, sub_self]
  obtain ⟨z, hz⟩ := hne
  have hz' : z ∈ Hpoly a' b' := by
    rw [heq]
    exact hz
  have hline' : ∀ t : ℝ, z + t • g ∈ Hpoly a' b' := by
    intro t j
    have hj := hz' j
    simp only [inner_add_right, inner_smul_right, hg' j, mul_zero, add_zero]
    exact hj
  have hline : ∀ t : ℝ, z + t • g ∈ Hpoly a b := by
    intro t
    rw [← heq]
    exact hline' t
  have hg : ∀ i : Fin n, ⟪a i, g⟫ = 0 := by
    intro i
    by_contra hgi
    let t : ℝ := (b i - ⟪a i, z⟫ + 1) / ⟪a i, g⟫
    have h := hline t i
    simp only [inner_add_right, inner_smul_right] at h
    have hmul : t * ⟪a i, g⟫ = b i - ⟪a i, z⟫ + 1 := by
      dsimp [t]
      exact div_mul_cancel₀ _ hgi
    linarith
  apply sub_eq_zero.mp
  apply hinj
  funext i
  change ⟪a i, g⟫ = ⟪a i, (0 : EuclideanSpace ℝ (Fin d))⟫
  simp [hg i]

/-- Any equivalent common-face subpresentation inherits injectivity from an
injective ambient presentation, provided the common face is feasible at its
source point. -/
theorem commonFace_subpresentation_rowMap_injective_of_injective
    {d n m : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b)
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (e : Fin m ↪ Fin n)
    (heq :
      Hpoly
          (fun j => commonFaceA a b u x (e j))
          (fun j => commonFaceB a b u x (e j)) =
        Hpoly (commonFaceA a b u x) (commonFaceB a b u x)) :
    Function.Injective
      (HirschCircuit.rowMap (fun j => commonFaceA a b u x (e j))) := by
  have hfull := rowMap_commonFaceA_injective_of_injective a b u x hinj
  have hzero :
      (0 : EuclideanSpace ℝ (Fin (commonFaceDim a b u x))) ∈
        Hpoly (commonFaceA a b u x) (commonFaceB a b u x) := by
    apply (mem_commonFace_coord_iff a b u x 0).2
    simpa [commonFacePoint] using commonFace_u_mem a b u x hu
  exact rowMap_injective_of_equivalent_nonempty_hpoly
    (commonFaceA a b u x) (commonFaceB a b u x)
    (fun j => commonFaceA a b u x (e j))
    (fun j => commonFaceB a b u x (e j))
    heq ⟨0, hzero⟩ hfull

/-- Every equivalent `m`-row presentation of a feasible common carrier in an
injective ambient H-polyhedron has at least its intrinsic dimension many rows.
This is the pointed replacement for the bounded minimum-carrier row-count
inequality used by the strict/blocker dichotomy. -/
theorem commonFaceDim_le_subpresentation_of_injective
    {d n m : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b)
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (e : Fin m ↪ Fin n)
    (heq :
      Hpoly
          (fun j => commonFaceA a b u x (e j))
          (fun j => commonFaceB a b u x (e j)) =
        Hpoly (commonFaceA a b u x) (commonFaceB a b u x)) :
    commonFaceDim a b u x ≤ m := by
  exact rows_ge_dimension_of_injective
    (fun j => commonFaceA a b u x (e j))
    (commonFace_subpresentation_rowMap_injective_of_injective
      a b u x hu hinj e heq)

#print axioms rowMap_commonFaceA_injective_of_injective
#print axioms rowMap_injective_of_equivalent_nonempty_hpoly
#print axioms commonFace_subpresentation_rowMap_injective_of_injective
#print axioms commonFaceDim_le_subpresentation_of_injective

end HirschCircuitLocalization
