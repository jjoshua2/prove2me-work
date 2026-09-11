import Solutions.PolynomialIrredundantRowCount
import Solutions.PolynomialCommonFaceMinimalSubpresentation

/-!
# Representation-independent meaning of the minimum common-face row count

Candidate source: not yet compiled or axiom-audited. These adapters upgrade
minimum-over-original-subsets semantics to minimum-over-arbitrary-presentations
semantics, provided a strictly feasible irredundant coordinate model exists.
They do not define or count an abstract geometric facet type.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped RealInnerProductSpace
open Hirsch

namespace HirschCircuitLocalization

/-- Any strictly feasible irredundant original-row subpresentation attains the
minimum common-face row count, not just an arbitrarily chosen deletion order. -/
theorem commonFace_minCount_eq_irredundant_subpresentation
    {d n m : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) (e : Fin m ↪ Fin n)
    (he : Hpoly
        (fun j => HirschCommonFace.commonFaceA a b u v (e j))
        (fun j => HirschCommonFace.commonFaceB a b u v (e j)) =
      Hpoly (HirschCommonFace.commonFaceA a b u v)
        (HirschCommonFace.commonFaceB a b u v))
    (hirr : RowPresentationIrredundant
      (fun j => HirschCommonFace.commonFaceA a b u v (e j))
      (fun j => HirschCommonFace.commonFaceB a b u v (e j)))
    (hstrict : StrictlyFeasibleRows
      (fun j => HirschCommonFace.commonFaceA a b u v (e j))
      (fun j => HirschCommonFace.commonFaceB a b u v (e j))) :
    commonFaceMinSubpresentationCount a b u v = m := by
  have hm : HirschCommonFace.CommonFaceHasSubpresentationAtMost a b u v m := by
    change HirschCommonFace.HasSubpresentationAtMost
      (HirschCommonFace.commonFaceA a b u v)
      (HirschCommonFace.commonFaceB a b u v) m
    exact ⟨m, le_rfl, e, he⟩
  have hminle := commonFaceMinSubpresentation_le a b u v m hm
  have hspec := commonFaceMinSubpresentation_spec a b u v
  change HirschCommonFace.HasSubpresentationAtMost
    (HirschCommonFace.commonFaceA a b u v)
    (HirschCommonFace.commonFaceB a b u v)
    (commonFaceMinSubpresentationCount a b u v) at hspec
  obtain ⟨r, hr, f, hf⟩ := hspec
  have hmr : m ≤ r := HirschRowCount.irredundant_rows_card_le_any_equivalent_presentation
    (fun j => HirschCommonFace.commonFaceA a b u v (e j))
    (fun j => HirschCommonFace.commonFaceB a b u v (e j))
    (fun j => HirschCommonFace.commonFaceA a b u v (f j))
    (fun j => HirschCommonFace.commonFaceB a b u v (f j))
    hirr hstrict (hf.trans he.symm)
  exact Nat.le_antisymm hminle (hmr.trans hr)

/-- The minimum original-row count equals the number of rows in ANY equivalent
strictly feasible irredundant coordinate presentation. Its normals need not
be inherited from the ambient polytope. This is a cross-presentation theorem,
not an identification with an abstract facet API. -/
theorem commonFace_minCount_eq_any_irredundant_presentation
    {d n m : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (c : Fin m → EuclideanSpace ℝ (Fin (HirschCommonFace.commonFaceDim a b u v)))
    (β : Fin m → ℝ)
    (hP : Hpoly c β =
      Hpoly (HirschCommonFace.commonFaceA a b u v)
        (HirschCommonFace.commonFaceB a b u v))
    (hirrC : RowPresentationIrredundant c β)
    (hstrictC : StrictlyFeasibleRows c β) :
    commonFaceMinSubpresentationCount a b u v = m := by
  let A := HirschCommonFace.commonFaceA a b u v
  let B := HirschCommonFace.commonFaceB a b u v
  obtain ⟨z, hz⟩ := hstrictC
  have hzC : z ∈ Hpoly c β := fun j => (hz j).le
  have hzA : z ∈ Hpoly A B := by rw [← hP]; exact hzC
  have hsep : ∀ j, A j ≠ 0 → ⟪A j, z⟫ ≠ B j ∨ ⟪A j, z⟫ ≠ B j := by
    intro j hj
    apply Or.inl
    have hlt := HirschRowCount.strict_on_nonzero_rows_strict_for_valid_row
      c β z hzC (fun k _ => hz k) (A j) (B j) hj (by
        intro y hy
        have hyA : y ∈ Hpoly A B := by rw [← hP]; exact hy
        exact hyA j)
    exact ne_of_lt hlt
  obtain ⟨r, _hr, e, he, hirr, hs⟩ :=
    HirschCircuit.exists_irredundant_strict_model
      (HirschCommonFace.commonFaceDim a b u v) n A B z z hzA hzA hsep
  have hminr : commonFaceMinSubpresentationCount a b u v = r :=
    commonFace_minCount_eq_irredundant_subpresentation a b u v e he hirr hs
  have hrm : r = m := HirschRowCount.equivalent_irredundant_row_counts_eq
    (fun j => A (e j)) (fun j => B (e j)) c β hirr hirrC hs (hP.trans he.symm)
  exact hminr.trans hrm

#print axioms commonFace_minCount_eq_irredundant_subpresentation
#print axioms commonFace_minCount_eq_any_irredundant_presentation

end HirschCircuitLocalization
