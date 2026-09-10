import Mathlib
import Solutions.PolynomialRowRankDeletion

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCircuitLocalization

open HirschPolynomialAccess

variable {d n : ℕ}

/-- Ambient rows whose normal restricts nontrivially to a chosen linear
subspace. These are exactly the rows that can contribute rank after passing to
that subspace. -/
noncomputable def effectiveRowsOnSubspace
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i =>
    ∃ x : W, ⟪a i, (x : EuclideanSpace ℝ (Fin d))⟫ ≠ 0)

/-- Removing rows that vanish identically on `W` does not change the kernel of
the row-evaluation map restricted to `W`. -/
theorem restricted_rowEval_effective_kernel_eq
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (S : Finset (Fin n)) :
    ((rowEvalMap a (S ∩ effectiveRowsOnSubspace a W)).domRestrict W).ker =
      ((rowEvalMap a S).domRestrict W).ker := by
  classical
  let E := effectiveRowsOnSubspace a W
  let A := (rowEvalMap a (S ∩ E)).domRestrict W
  let B := (rowEvalMap a S).domRestrict W
  change A.ker = B.ker
  ext x
  constructor
  · intro hx
    have hA0 : A x = 0 := LinearMap.mem_ker.1 hx
    apply LinearMap.mem_ker.2
    funext i
    change ⟪a i.1, (x : EuclideanSpace ℝ (Fin d))⟫ = 0
    by_cases hiE : i.1 ∈ E
    · have hiSE : i.1 ∈ S ∩ E := Finset.mem_inter.2 ⟨i.2, hiE⟩
      exact congrFun hA0 ⟨i.1, hiSE⟩
    · have hnone : ¬ ∃ y : W,
          ⟪a i.1, (y : EuclideanSpace ℝ (Fin d))⟫ ≠ 0 := by
        simpa [E, effectiveRowsOnSubspace] using hiE
      by_contra hne
      exact hnone ⟨x, hne⟩
  · intro hx
    have hB0 : B x = 0 := LinearMap.mem_ker.1 hx
    apply LinearMap.mem_ker.2
    funext i
    change ⟪a i.1, (x : EuclideanSpace ℝ (Fin d))⟫ = 0
    exact congrFun hB0 ⟨i.1, (Finset.mem_inter.1 i.2).1⟩

/-- Rank version of `restricted_rowEval_effective_kernel_eq`. -/
theorem restricted_rowEval_effective_rank_eq
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (S : Finset (Fin n)) :
    Module.finrank ℝ
        (((rowEvalMap a (S ∩ effectiveRowsOnSubspace a W)).domRestrict W).range) =
      Module.finrank ℝ (((rowEvalMap a S).domRestrict W).range) := by
  let A := (rowEvalMap a (S ∩ effectiveRowsOnSubspace a W)).domRestrict W
  let B := (rowEvalMap a S).domRestrict W
  have hker : A.ker = B.ker := by
    simpa [A, B] using restricted_rowEval_effective_kernel_eq a W S
  have hA := A.finrank_range_add_finrank_ker
  have hB := B.finrank_range_add_finrank_ker
  rw [hker] at hA
  exact Nat.add_right_cancel (hA.trans hB.symm)

/-- The rows that remain nontrivial on the common-face direction satisfy the
basic ambient count budget

`effective rows + ambient dimension ≤ original rows + common-face dimension`.

No vertex, circuit, irredundancy, or boundedness assumption is needed: this is
purely the rank-nullity cost of imposing the common tight equations. -/
theorem commonDirection_effectiveRows_card_add_dim_le_rows_add_faceDim
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) :
    (effectiveRowsOnSubspace a (commonDirection a b u v)).card + d ≤
      n + commonFaceDim a b u v := by
  classical
  let C := commonSourceRows a b u v
  let W := commonDirection a b u v
  let E := effectiveRowsOnSubspace a W
  let T := rowEvalMap a C
  have hCE : Disjoint C E := by
    refine Finset.disjoint_left.2 ?_
    intro i hiC hiE
    have hex : ∃ x : W,
        ⟪a i, (x : EuclideanSpace ℝ (Fin d))⟫ ≠ 0 := by
      simpa [E, effectiveRowsOnSubspace] using hiE
    obtain ⟨x, hx⟩ := hex
    have hxker : (x : EuclideanSpace ℝ (Fin d)) ∈ T.ker := by
      simpa [T, W, C, commonDirection] using x.property
    have hzero : T (x : EuclideanSpace ℝ (Fin d)) = 0 :=
      LinearMap.mem_ker.1 hxker
    have hcoord := congrFun hzero ⟨i, hiC⟩
    exact hx hcoord
  have htotal : C.card + E.card ≤ n := by
    have hcard : (C ∪ E).card = C.card + E.card :=
      Finset.card_union_of_disjoint hCE
    have hsub : C ∪ E ⊆ (Finset.univ : Finset (Fin n)) := by simp
    have hle := Finset.card_le_card hsub
    rw [hcard] at hle
    simpa using hle
  have hnull : Module.finrank ℝ T.range + Module.finrank ℝ W = d := by
    have h := T.finrank_range_add_finrank_ker
    have hdom : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
      finrank_euclideanSpace_fin (𝕜 := ℝ)
    rw [hdom] at h
    simpa [T, W, C, commonDirection] using h
  have hrange : Module.finrank ℝ T.range ≤ C.card := by
    calc
      Module.finrank ℝ T.range ≤ Module.finrank ℝ (C → ℝ) :=
        Submodule.finrank_le _
      _ = C.card := by simp [Fintype.card_coe]
  have hdim : d ≤ C.card + Module.finrank ℝ W := by omega
  have hmain : E.card + d ≤ n + Module.finrank ℝ W := by omega
  simpa [E, W, commonFaceDim] using hmain

/-- On a common face of a row-circuit pair, discarding ambient rows that become
identically zero does not change the exact neutral rank `h-1`. -/
theorem rowCircuit_effectiveNeutral_rank_on_commonDirection_eq_faceDim_sub_one
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u)) :
    Module.finrank ℝ
        (((rowEvalMap a
          (circuitNeutralRows a (v - u) ∩
            effectiveRowsOnSubspace a (commonDirection a b u v))).domRestrict
          (commonDirection a b u v)).range) =
      commonFaceDim a b u v - 1 := by
  rw [restricted_rowEval_effective_rank_eq]
  exact rowCircuit_neutral_rank_on_commonDirection_eq_commonFaceDim_sub_one
    a b u v hu hcirc

#print axioms restricted_rowEval_effective_kernel_eq
#print axioms restricted_rowEval_effective_rank_eq
#print axioms commonDirection_effectiveRows_card_add_dim_le_rows_add_faceDim
#print axioms rowCircuit_effectiveNeutral_rank_on_commonDirection_eq_faceDim_sub_one

end HirschCircuitLocalization
