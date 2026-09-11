import Mathlib
import Solutions.PolynomialCircuitCheckpointMinSubpresentationDefect

open scoped BigOperators RealInnerProductSpace
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- For any bounded parent and any feasible source checkpoint, the minimum
coordinate-row presentation excess of its common carrier never exceeds the
ambient row excess `n-d`. No circuit or endpoint-vertex hypothesis is needed. -/
theorem commonFace_minSubpresentation_excess_le_parent_excess_of_bounded_feasible
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hx : x ∈ Hpoly a b) :
    commonFaceMinSubpresentationCount a b x y - commonFaceDim a b x y ≤ n - d := by
  classical
  let M := commonFaceMinSubpresentationCount a b x y
  let h := commonFaceDim a b x y
  obtain ⟨e, _he, hFeq⟩ :=
    commonFace_minSubpresentation_effective_witness_of_feasible a b x y hx
  let F : Finset (Fin n) :=
    (Finset.univ.map e) ∩ HirschCommonFace.commonFaceEffectiveRows a b x y
  let E : Finset (Fin n) := effectiveRowsOnSubspace a (commonDirection a b x y)
  have hFM : F.card = M := by simpa [F, M] using hFeq
  have hFE : F ⊆ E := by
    intro i hiF
    have hpub : i ∈ HirschCommonFace.commonFaceEffectiveRows a b x y :=
      Finset.inter_subset_right hiF
    have hi : i ∈ effectiveRowsOnSubspace a (commonDirection a b x y) := by
      rw [effectiveRowsOn_commonDirection_eq_publicCommonFaceEffectiveRows]
      exact hpub
    simpa [E] using hi
  have hFcard : F.card ≤ E.card := Finset.card_le_card hFE
  have hbudget : E.card + d ≤ n + h := by
    simpa [E, h] using
      commonDirection_effectiveRows_card_add_dim_le_rows_add_faceDim a b x y
  have hMd : M + d ≤ n + h := by omega
  have hhM : h ≤ M := by
    simpa [h, M] using
      commonFaceDim_le_minSubpresentation_of_bounded_feasible a b x y hbd hx
  have hinj := HirschCircuit.rowMap_injective_of_bounded a b hbd x hx
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  have hdn : d ≤ n := by
    simpa [HirschCircuit.rowMap, finrank_euclideanSpace_fin] using hdim
  change M - h ≤ n - d
  omega

/-- Equivalent non-subtractive form of the same invariant. -/
theorem commonFace_minSubpresentationCount_le_faceDim_add_parent_excess
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hx : x ∈ Hpoly a b) :
    commonFaceMinSubpresentationCount a b x y ≤
      commonFaceDim a b x y + (n - d) := by
  have hex := commonFace_minSubpresentation_excess_le_parent_excess_of_bounded_feasible
    a b x y hbd hx
  have hdim := commonFaceDim_le_minSubpresentation_of_bounded_feasible a b x y hbd hx
  omega

/-- Concrete witness form: every common carrier based at a feasible checkpoint
has an equivalent original-row coordinate presentation with at most
`h + (n-d)` rows. Thus restricting to a carrier does not increase row excess. -/
theorem commonFace_has_subpresentation_faceDim_add_parent_excess
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hx : x ∈ Hpoly a b) :
    HirschCommonFace.CommonFaceHasSubpresentationAtMost a b x y
      (commonFaceDim a b x y + (n - d)) := by
  have hspec := commonFaceMinSubpresentation_spec a b x y
  change HirschCommonFace.HasSubpresentationAtMost
    (commonFaceA a b x y) (commonFaceB a b x y)
    (commonFaceMinSubpresentationCount a b x y) at hspec
  obtain ⟨m, hm, e, he⟩ := hspec
  refine ⟨m, ?_, e, he⟩
  exact hm.trans
    (commonFace_minSubpresentationCount_le_faceDim_add_parent_excess
      a b x y hbd hx)

#print axioms commonFace_minSubpresentation_excess_le_parent_excess_of_bounded_feasible
#print axioms commonFace_minSubpresentationCount_le_faceDim_add_parent_excess
#print axioms commonFace_has_subpresentation_faceDim_add_parent_excess

end HirschCircuitLocalization
