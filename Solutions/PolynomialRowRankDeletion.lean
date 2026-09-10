import Mathlib
import Solutions.PolynomialCircuitFaceNeutralRank

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCircuitLocalization

open HirschPolynomialAccess

variable {d n : ℕ}

/-- Deleting rows from a restricted row-evaluation system lowers its linear
rank by no more than the number of deleted rows. This is the finite-dimensional
rank-loss estimate needed when passing from all restricted ambient inequalities
to a selected irredundant face presentation. -/
theorem restricted_rowEval_rank_le_subrank_add_deleted
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (S T : Finset (Fin n))
    (hST : S ⊆ T) :
    Module.finrank ℝ (((rowEvalMap a T).domRestrict W).range) ≤
      Module.finrank ℝ (((rowEvalMap a S).domRestrict W).range) +
        (T \ S).card := by
  classical
  let D := T \ S
  let A := (rowEvalMap a S).domRestrict W
  let B := (rowEvalMap a D).domRestrict W
  let Q := (rowEvalMap a T).domRestrict W
  let P : W →ₗ[ℝ] A.range × (D → ℝ) :=
    LinearMap.prod A.rangeRestrict B
  have hker : P.ker = Q.ker := by
    ext x
    constructor
    · intro hx
      have hp0 : P x = 0 := LinearMap.mem_ker.1 hx
      change (A.rangeRestrict x, B x) = (0, 0) at hp0
      have hA0 : A x = 0 := by
        have hfst : A.rangeRestrict x = 0 := congrArg Prod.fst hp0
        exact congrArg Subtype.val hfst
      have hB0 : B x = 0 := congrArg Prod.snd hp0
      apply LinearMap.mem_ker.2
      funext i
      change ⟪a i.1, (x : EuclideanSpace ℝ (Fin d))⟫ = 0
      by_cases hiS : i.1 ∈ S
      · exact congrFun hA0 ⟨i.1, hiS⟩
      · have hiD : i.1 ∈ D := by
          exact Finset.mem_sdiff.mpr ⟨i.2, hiS⟩
        exact congrFun hB0 ⟨i.1, hiD⟩
    · intro hx
      have hQ0 : Q x = 0 := LinearMap.mem_ker.1 hx
      apply LinearMap.mem_ker.2
      change (A.rangeRestrict x, B x) = (0, 0)
      apply Prod.ext
      · apply Subtype.ext
        funext i
        change ⟪a i.1, (x : EuclideanSpace ℝ (Fin d))⟫ = 0
        exact congrFun hQ0 ⟨i.1, hST i.2⟩
      · funext i
        change ⟪a i.1, (x : EuclideanSpace ℝ (Fin d))⟫ = 0
        have hiT : i.1 ∈ T := (Finset.mem_sdiff.1 i.2).1
        exact congrFun hQ0 ⟨i.1, hiT⟩
  have hPnull := P.finrank_range_add_finrank_ker
  have hQnull := Q.finrank_range_add_finrank_ker
  rw [hker] at hPnull
  have hrankEq : Module.finrank ℝ P.range = Module.finrank ℝ Q.range := by
    exact Nat.add_right_cancel (hPnull.trans hQnull.symm)
  have hbound : Module.finrank ℝ P.range ≤
      Module.finrank ℝ A.range + D.card := by
    calc
      Module.finrank ℝ P.range ≤
          Module.finrank ℝ (A.range × (D → ℝ)) :=
        Submodule.finrank_le _
      _ = Module.finrank ℝ A.range + D.card := by
        simp [Fintype.card_coe]
  have hmain : Module.finrank ℝ Q.range ≤
      Module.finrank ℝ A.range + D.card := by
    rw [← hrankEq]
    exact hbound
  simpa [Q, A, D] using hmain

/-- Defect form of the same estimate: if the larger restricted row system has
rank `h-1`, then the missing rank after keeping only `S` is bounded by the
number of removed rows. -/
theorem restricted_rowEval_defect_le_deleted
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (S T : Finset (Fin n))
    (hST : S ⊆ T)
    (hfull : Module.finrank ℝ (((rowEvalMap a T).domRestrict W).range) =
      Module.finrank ℝ W - 1) :
    (Module.finrank ℝ W - 1) -
        Module.finrank ℝ (((rowEvalMap a S).domRestrict W).range) ≤
      (T \ S).card := by
  have hle := restricted_rowEval_rank_le_subrank_add_deleted a W S T hST
  rw [hfull] at hle
  omega

#print axioms restricted_rowEval_rank_le_subrank_add_deleted
#print axioms restricted_rowEval_defect_le_deleted

end HirschCircuitLocalization
