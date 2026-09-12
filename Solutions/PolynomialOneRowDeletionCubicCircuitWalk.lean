import Mathlib
import Solutions.PolynomialInjectiveCubicCircuitWalk
import Solutions.PolynomialOneRowDeletionPointedness
import Solutions.PolynomialOneRowDeletionCapWitness

open scoped RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschDeletion

/-- Canonical finite reindexing of all rows except one distinguished row. -/
noncomputable def rowsWithoutEquiv
    {n : ℕ} (j : Fin n) :
    Fin (Fintype.card {i : Fin n // i ≠ j}) ≃ {i : Fin n // i ≠ j} :=
  (Fintype.equivFin {i : Fin n // i ≠ j}).symm

/-- Row normals of the one-row deletion outer, reindexed by a `Fin` type so
that they can be used directly by the row-circuit API. -/
noncomputable def rowsWithout
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (j : Fin n) :
    Fin (Fintype.card {i : Fin n // i ≠ j}) → EuclideanSpace ℝ (Fin d) :=
  fun k => a ((rowsWithoutEquiv j k).1)

/-- Right-hand sides of the one-row deletion outer under the same canonical
`Fin` reindexing. -/
noncomputable def rhsWithout
    {n : ℕ}
    (b : Fin n → ℝ) (j : Fin n) :
    Fin (Fintype.card {i : Fin n // i ≠ j}) → ℝ :=
  fun k => b ((rowsWithoutEquiv j k).1)

/-- The number of retained rows after deleting one row is at most the original
row count.  We only need this inequality for polynomial accounting; no exact
`n-1` arithmetic is required. -/
theorem rowsWithout_card_le
    {n : ℕ} (j : Fin n) :
    Fintype.card {i : Fin n // i ≠ j} ≤ n := by
  classical
  have hcard := Fintype.card_le_of_injective
    (fun i : {i : Fin n // i ≠ j} => i.1)
    (fun x y h => Subtype.ext h)
  simpa only [Fintype.card_fin] using hcard

/-- The canonical `Fin` reindexing describes exactly the same deletion outer
used by the exterior-cap modules. -/
theorem hpoly_rowsWithout_eq_deletionOuterSet
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (j : Fin n) :
    Hpoly (rowsWithout a j) (rhsWithout b j) =
      HirschCapVertices.deletionOuterSet a b j := by
  classical
  ext y
  change
    (∀ k : Fin (Fintype.card {i : Fin n // i ≠ j}),
      ⟪rowsWithout a j k, y⟫ ≤ rhsWithout b j k) ↔
    (∀ i : Fin n, i ≠ j → ⟪a i, y⟫ ≤ b i)
  constructor
  · intro h i hij
    let si : {i : Fin n // i ≠ j} := ⟨i, hij⟩
    let k : Fin (Fintype.card {i : Fin n // i ≠ j}) :=
      Fintype.equivFin {i : Fin n // i ≠ j} si
    have hk := h k
    simpa [rowsWithout, rhsWithout, rowsWithoutEquiv, k, si] using hk
  · intro h k
    exact h (rowsWithoutEquiv j k).1 (rowsWithoutEquiv j k).2

/-- Reindexing the remaining rows preserves the injectivity supplied by the
one-row deletion pointedness theorem. -/
theorem rowMap_rowsWithout_injective_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b)
    (j : Fin n) :
    Function.Injective (HirschCircuit.rowMap (rowsWithout a j)) := by
  classical
  have hinj := rowMapWithout_injective_of_bounded a b hbd x hx j
  intro p q hpq
  apply hinj
  funext i
  let k : Fin (Fintype.card {i : Fin n // i ≠ j}) :=
    Fintype.equivFin {i : Fin n // i ≠ j} i
  have hk := congrFun hpq k
  change ⟪a i.1, p⟫ = ⟪a i.1, q⟫
  simpa [HirschCircuit.rowMap, rowsWithout, rowsWithoutEquiv, k] using hk

/-- Every feasible point of a one-row deletion outer reaches any vertex of that
outer by a padded row-circuit walk of length `17*m^3`, where `m` is the number
of retained rows and `m ≤ n`.

Crucially, the deletion outer is allowed to be unbounded.  Boundedness is used
only for the original parent presentation, in order to prove that deleting one
row leaves an injective row map.  The cubic circuit construction itself then
runs on the pointed unbounded outer. -/
theorem rowCircuitWalk_explicit_cubic_of_one_row_deletion
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b)
    (j : Fin n)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly (rowsWithout a j) (rhsWithout b j))
    (hv : v ∈ extremePoints ℝ (Hpoly (rowsWithout a j) (rhsWithout b j))) :
    RowCircuitWalk
      (rowsWithout a j) (rhsWithout b j)
      (17 * (Fintype.card {i : Fin n // i ≠ j}) ^ 3) u v := by
  exact HirschCircuit.rowCircuitWalk_explicit_cubic_of_injective
    (rowsWithout a j) (rhsWithout b j)
    (rowMap_rowsWithout_injective_of_bounded a b hbd x hx j)
    u v hu hv

/-- Exterior-cap-facing form of the previous theorem.  Its hypotheses are
stated directly on `deletionOuterSet`, the same unbounded outer set used by the
far-cap vertex classification. -/
theorem rowCircuitWalk_explicit_cubic_of_deletionOuterSet
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b)
    (j : Fin n)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ HirschCapVertices.deletionOuterSet a b j)
    (hv : v ∈ extremePoints ℝ (HirschCapVertices.deletionOuterSet a b j)) :
    RowCircuitWalk
      (rowsWithout a j) (rhsWithout b j)
      (17 * (Fintype.card {i : Fin n // i ≠ j}) ^ 3) u v := by
  have hmodel := hpoly_rowsWithout_eq_deletionOuterSet a b j
  apply rowCircuitWalk_explicit_cubic_of_one_row_deletion a b hbd x hx j u v
  · rwa [hmodel]
  · rwa [hmodel]

#print axioms rowsWithout_card_le
#print axioms hpoly_rowsWithout_eq_deletionOuterSet
#print axioms rowMap_rowsWithout_injective_of_bounded
#print axioms rowCircuitWalk_explicit_cubic_of_one_row_deletion
#print axioms rowCircuitWalk_explicit_cubic_of_deletionOuterSet

end HirschDeletion
