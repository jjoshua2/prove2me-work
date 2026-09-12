import Mathlib
import Solutions.PolynomialCircuitInjectiveNeutralRank
import Solutions.PolynomialCircuitStepProgress
import Solutions.PolynomialOneRowDeletionCubicCircuitWalk

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- Exact neutral rank has a stronger form useful for row deletion: the neutral
rows of an injective row circuit, together with any one nonneutral row, already
separate ambient directions. -/
theorem rowCircuit_neutral_insert_rowEval_injective
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (g : EuclideanSpace ℝ (Fin d))
    (hg : IsRowCircuit a g)
    (i : Fin n) (hi : ⟪a i, g⟫ ≠ 0) :
    Function.Injective
      (rowEvalMap a (insert i (circuitNeutralRows a g))) := by
  classical
  let Z := circuitNeutralRows a g
  let S := insert i Z
  intro x y hxy
  let q := x - y
  have hqS : rowEvalMap a S q = 0 := by
    change rowEvalMap a S (x - y) = 0
    rw [map_sub, hxy, sub_self]
  have hqZ : rowEvalMap a Z q = 0 := by
    funext k
    have hk := congrFun hqS ⟨k.1, Finset.mem_insert_of_mem k.2⟩
    exact hk
  have hqker : q ∈ (rowEvalMap a Z).ker := LinearMap.mem_ker.mpr hqZ
  have hker := rowCircuit_neutral_kernel_eq_span_of_injective a hinj g hg
  change (rowEvalMap a Z).ker = _ at hker
  rw [hker] at hqker
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hqker
  have hiq := congrFun hqS ⟨i, Finset.mem_insert_self i Z⟩
  change ⟪a i, q⟫ = 0 at hiq
  rw [hc, inner_smul_right] at hiq
  have hc0 : c = 0 := (mul_eq_zero.mp hiq).resolve_right hi
  have hq0 : q = 0 := by rw [hc, hc0, zero_smul]
  exact sub_eq_zero.mp hq0

/-- Any selected row set containing all neutral rows and one nonneutral row of
an injective circuit also has injective row evaluation. -/
theorem rowCircuit_selected_rowEval_injective_of_neutral_insert_subset
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (g : EuclideanSpace ℝ (Fin d))
    (hg : IsRowCircuit a g)
    (i : Fin n) (hi : ⟪a i, g⟫ ≠ 0)
    (F : Finset (Fin n))
    (hsub : insert i (circuitNeutralRows a g) ⊆ F) :
    Function.Injective (rowEvalMap a F) := by
  classical
  have hsmall := rowCircuit_neutral_insert_rowEval_injective a hinj g hg i hi
  intro x y hxy
  apply hsmall
  funext k
  exact congrFun hxy ⟨k.1, hsub k.2⟩

/-- If a row circuit has two distinct nonneutral rows `i` and `j`, deleting
`j` preserves injectivity because the neutral rows plus the retained row `i`
already have full rank. -/
theorem rowCircuit_rowEval_erase_injective_of_two_nonneutral
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (g : EuclideanSpace ℝ (Fin d))
    (hg : IsRowCircuit a g)
    (i j : Fin n)
    (hi : ⟪a i, g⟫ ≠ 0) (hj : ⟪a j, g⟫ ≠ 0)
    (hij : i ≠ j) :
    Function.Injective (rowEvalMap a (Finset.univ.erase j)) := by
  classical
  apply rowCircuit_selected_rowEval_injective_of_neutral_insert_subset
    a hinj g hg i hi (Finset.univ.erase j)
  intro k hk
  rcases Finset.mem_insert.mp hk with hki | hkZ
  · subst k
    exact Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩
  · have hkj : k ≠ j := by
      intro h
      subst k
      have hz := (Finset.mem_filter.mp hkZ).2.2
      exact hj hz
    exact Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ _⟩

/-- A nontrivial maximal circuit step leaving a parent vertex has opposite-sign
support rows: one row is tight at the source and decreases strictly, while a
new blocking row is tight at the destination and increases strictly. -/
theorem rowCircuitStep_from_vertex_exists_signed_blockers
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hstep : RowCircuitStep a b x y) :
    ∃ i j : Fin n,
      i ≠ j ∧
      ⟪a i, x⟫ = b i ∧ ⟪a i, y - x⟫ < 0 ∧
      ⟪a j, y⟫ = b j ∧ 0 < ⟪a j, y - x⟫ := by
  classical
  let g := y - x
  have hsource : ∃ i : Fin n,
      ⟪a i, x⟫ = b i ∧ ⟪a i, g⟫ < 0 := by
    by_contra hnone
    push Not at hnone
    have hall : ∀ i : Fin n, ⟪a i, x⟫ = b i → ⟪a i, g⟫ = 0 := by
      intro i hix
      have hle : ⟪a i, g⟫ ≤ 0 := by
        dsimp [g]
        rw [inner_sub_right, hix]
        exact sub_nonpos.mpr (hstep.2.1 i)
      have hnlt : ¬ ⟪a i, g⟫ < 0 := hnone i hix
      exact le_antisymm hle (le_of_not_gt hnlt)
    have hg0 := HirschPolynomialAccess.vertex_tight_rows_span_checked
      d n a b x hx g hall
    exact hstep.2.2.1.1 hg0
  obtain ⟨i, hix, hineg⟩ := hsource
  obtain ⟨j, _, hjy, hjpos⟩ :=
    rowCircuitStep_exists_target_blocking_row a b x y hstep
  have hij : i ≠ j := by
    intro h
    subst j
    linarith
  exact ⟨i, j, hij, hix, hineg, hjy, hjpos⟩

#print axioms rowCircuit_neutral_insert_rowEval_injective
#print axioms rowCircuit_selected_rowEval_injective_of_neutral_insert_subset
#print axioms rowCircuit_rowEval_erase_injective_of_two_nonneutral
#print axioms rowCircuitStep_from_vertex_exists_signed_blockers

end HirschCircuitLocalization

namespace HirschDeletion

open HirschCircuitLocalization

/-- Reindexing after deleting one of two distinct nonneutral rows preserves an
injective row map. This is the `Fin`-indexed form needed by the circuit-walk
API. -/
theorem rowMap_rowsWithout_injective_of_two_nonneutral_rowCircuit
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (g : EuclideanSpace ℝ (Fin d))
    (hg : IsRowCircuit a g)
    (i j : Fin n)
    (hi : ⟪a i, g⟫ ≠ 0) (hj : ⟪a j, g⟫ ≠ 0)
    (hij : i ≠ j) :
    Function.Injective (HirschCircuit.rowMap (rowsWithout a j)) := by
  classical
  have herase := rowCircuit_rowEval_erase_injective_of_two_nonneutral
    a hinj g hg i j hi hj hij
  intro p q hpq
  apply herase
  funext k
  have hkj : k.1 ≠ j := (Finset.mem_erase.mp k.2).1
  let sk : {r : Fin n // r ≠ j} := ⟨k.1, hkj⟩
  let t : Fin (Fintype.card {r : Fin n // r ≠ j}) :=
    Fintype.equivFin {r : Fin n // r ≠ j} sk
  have ht := congrFun hpq t
  change ⟪a k.1, p⟫ = ⟪a k.1, q⟫
  simpa [HirschCircuit.rowMap, rowsWithout, rowsWithoutEquiv, t, sk] using ht

/-- A maximal circuit step from a vertex in an injective presentation admits
both a source-row deletion and a target-blocker deletion that strictly lower the
row count while preserving pointedness. -/
theorem rowCircuitStep_from_vertex_exists_two_pointed_row_deletions
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hstep : RowCircuitStep a b x y) :
    ∃ i j : Fin n,
      i ≠ j ∧
      ⟪a i, x⟫ = b i ∧ ⟪a i, y - x⟫ < 0 ∧
      ⟪a j, y⟫ = b j ∧ 0 < ⟪a j, y - x⟫ ∧
      Function.Injective (HirschCircuit.rowMap (rowsWithout a i)) ∧
      Function.Injective (HirschCircuit.rowMap (rowsWithout a j)) := by
  obtain ⟨i, j, hij, hix, hineg, hjy, hjpos⟩ :=
    rowCircuitStep_from_vertex_exists_signed_blockers a b x y hx hstep
  have hi : ⟪a i, y - x⟫ ≠ 0 := ne_of_lt hineg
  have hj : ⟪a j, y - x⟫ ≠ 0 := ne_of_gt hjpos
  have hdelI := rowMap_rowsWithout_injective_of_two_nonneutral_rowCircuit
    a hinj (y - x) hstep.2.2.1 j i hj hi hij.symm
  have hdelJ := rowMap_rowsWithout_injective_of_two_nonneutral_rowCircuit
    a hinj (y - x) hstep.2.2.1 i j hi hj hij
  exact ⟨i, j, hij, hix, hineg, hjy, hjpos, hdelI, hdelJ⟩

#print axioms rowMap_rowsWithout_injective_of_two_nonneutral_rowCircuit
#print axioms rowCircuitStep_from_vertex_exists_two_pointed_row_deletions

end HirschDeletion
