import Mathlib
import Solutions.PolynomialFaceEffectiveRows

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 3500000

noncomputable section

namespace HirschPolynomialAccess

/-- A row common to the two defining vertices vanishes after restriction to
the common-face direction space. -/
theorem commonFaceA_eq_zero_of_common_row {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (p q : EuclideanSpace ℝ (Fin d)) (i : Fin n)
    (hi : i ∈ commonSourceRows a b p q) :
    commonFaceA a b p q i = 0 := by
  let A := commonFaceA a b p q i
  have hlift : commonFaceLift a b p q A ∈ commonDirection a b p q :=
    commonFaceLift_mem_direction a b p q A
  have hker : rowEvalMap a (commonSourceRows a b p q)
      (commonFaceLift a b p q A) = 0 := LinearMap.mem_ker.1 hlift
  have horth : ⟪a i, commonFaceLift a b p q A⟫ = 0 :=
    congrFun hker ⟨i, hi⟩
  have hself : ⟪A, A⟫ = 0 := by
    rw [commonFace_inner_restricted]
    exact horth
  by_contra hA
  exact (ne_of_gt (real_inner_self_pos.mpr hA)) hself

/-- Effective rows and common rows are disjoint. -/
theorem disjoint_effective_common_rows {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (p q : EuclideanSpace ℝ (Fin d)) :
    Disjoint (commonFaceEffectiveRows a b p q) (commonSourceRows a b p q) := by
  refine Finset.disjoint_left.2 ?_
  intro i hie hic
  have hne : commonFaceA a b p q i ≠ 0 := by
    simpa [commonFaceEffectiveRows] using hie
  exact hne (commonFaceA_eq_zero_of_common_row a b p q i hic)

/-- The effective row count is at most the total row count minus the number
of rows common to the two vertices. -/
theorem commonFaceEffectiveCount_le_sub_common_card {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (p q : EuclideanSpace ℝ (Fin d)) :
    commonFaceEffectiveCount a b p q ≤ n - (commonSourceRows a b p q).card := by
  classical
  let E := commonFaceEffectiveRows a b p q
  let C := commonSourceRows a b p q
  have hdisj : Disjoint E C := by
    simpa [E, C] using disjoint_effective_common_rows a b p q
  have htotal : E.card + C.card ≤ n := by
    rw [← Finset.card_union_of_disjoint hdisj]
    have hsub : E ∪ C ⊆ (Finset.univ : Finset (Fin n)) := by simp
    simpa using Finset.card_le_card hsub
  change E.card ≤ n - C.card
  omega

#print axioms commonFaceA_eq_zero_of_common_row
#print axioms disjoint_effective_common_rows
#print axioms commonFaceEffectiveCount_le_sub_common_card

end HirschPolynomialAccess
