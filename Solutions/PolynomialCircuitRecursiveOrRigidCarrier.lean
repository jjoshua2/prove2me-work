import Mathlib
import Solutions.PolynomialLowerExcessCarrierRecursion
import Solutions.PolynomialCircuitIrredundantMinCarrierDichotomy

open scoped BigOperators RealInnerProductSpace
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- The rigid equality-side certificate left after row-excess induction has
already discharged every common carrier of strictly smaller minimum
presentation excess.

The selected carrier model is irredundant, strictly feasible, and globally
minimum-cardinality.  Its row excess is exactly the ambient row excess, and an
indispensable row is a same-phase trapped blocker with a single-tight witness. -/
def EqualExcessEssentialPhaseBlocker
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y v : EuclideanSpace ℝ (Fin d))
    (M : ℝ) (r : Fin n → ℝ) : Prop :=
  ∃ m : ℕ, m ≤ n ∧ ∃ e : Fin m ↪ Fin n,
    Hpoly
        (fun j => HirschCommonFace.commonFaceA a b x y (e j))
        (fun j => HirschCommonFace.commonFaceB a b x y (e j)) =
      Hpoly
        (HirschCommonFace.commonFaceA a b x y)
        (HirschCommonFace.commonFaceB a b x y) ∧
    RowPresentationIrredundant
        (fun j => HirschCommonFace.commonFaceA a b x y (e j))
        (fun j => HirschCommonFace.commonFaceB a b x y (e j)) ∧
    StrictlyFeasibleRows
        (fun j => HirschCommonFace.commonFaceA a b x y (e j))
        (fun j => HirschCommonFace.commonFaceB a b x y (e j)) ∧
    commonFaceMinSubpresentationCount a b x y = m ∧
    m - commonFaceDim a b x y = n - d ∧
    ∃ j : Fin m,
      e j ∈ targetOnlyRows a b x y ∧
      ⟪a (e j), v⟫ < b (e j) ∧
      r (e j) ≤ M * HirschCircuit.slack a b v (e j) ∧
      HirschCircuit.slack a b y (e j) = 0 ∧
      HirschCircuit.slack a b y (e j) < HirschCircuit.slack a b x (e j) ∧
      ∃ q : EuclideanSpace ℝ (Fin (commonFaceDim a b x y)),
        ⟪HirschCommonFace.commonFaceA a b x y (e j), q⟫ =
          HirschCommonFace.commonFaceB a b x y (e j) ∧
        ∀ k : Fin m, k ≠ j →
          ⟪HirschCommonFace.commonFaceA a b x y (e k), q⟫ <
            HirschCommonFace.commonFaceB a b x y (e k)

/-- The minimum original-row presentation excess of every maximal row-circuit
carrier is at most the ambient row excess.  This forgets the nonnegative
neutral-rank defect from the stronger checkpoint accounting theorem and exposes
the monotone induction parameter directly. -/
theorem rowCircuitStep_minPresentationExcess_le_ambient
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hstep : RowCircuitStep a b x y) :
    commonFaceMinSubpresentationCount a b x y -
        commonFaceDim a b x y ≤ n - d := by
  obtain ⟨_e, _heq, _hcard, hbudget⟩ :=
    rowCircuit_commonFace_minSubpresentation_excess_defect_of_bounded
      a b x y hbd hstep.1 hstep.2.2.1
  have hbudget' := hbudget
  change
    (commonFaceMinSubpresentationCount a b x y -
        commonFaceDim a b x y) + _ ≤ n - d at hbudget'
  omega

/-- Row-excess induction in the exact form needed by the same-phase circuit
construction.

Assume all bounded nonempty H-polyhedra of row excess strictly below the parent
excess already have diameter at most `B`.  Then every maximal circuit step
remaining inside one phase has exactly two outcomes:

* its common carrier has strictly smaller minimum presentation excess and is
  therefore already recursively routable with diameter `B`; or
* the carrier has **equal** row excess `n-d`, and an indispensable row of a
  minimum irredundant carrier model is a trapped target-positive blocker whose
  slack falls to zero on this step.

Thus neutral-rank defect is no longer part of the induction parameter.  The
only unresolved branch is the rigid equal-excess geometry. -/
theorem rowCircuitStep_same_phase_recursive_or_equalExcess_essential_trapped_blocker
    {B d n : ℕ}
    (hIH : LowerExcessHpolyDiameterBound (n - d) B)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hstep : RowCircuitStep a b x y)
    (hv : v ∈ Hpoly a b)
    (M : ℝ) (hM : 0 ≤ M) (r : Fin n → ℝ)
    (heqx :
      HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v) r =
        HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v)
          (HirschCircuit.slack a b x))
    (heqy :
      HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v) r =
        HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v)
          (HirschCircuit.slack a b y)) :
    DiamLE (commonFace a b x y) B ∨
      EqualExcessEssentialPhaseBlocker a b x y v M r := by
  have hle := rowCircuitStep_minPresentationExcess_le_ambient
    a b x y hbd hstep
  by_cases hlt :
      commonFaceMinSubpresentationCount a b x y -
          commonFaceDim a b x y < n - d
  · left
    exact commonFace_diamLE_of_minPresentationExcess_lt
      hIH a b x y hbd hstep.1 hlt
  · have heqEx :
        commonFaceMinSubpresentationCount a b x y -
            commonFaceDim a b x y = n - d := by
      omega
    right
    obtain ⟨m, hm, e, heq, hirr, hstrictRows, hmin, hsplit⟩ :=
      rowCircuitStep_irredundant_minPresentation_same_phase_strict_budget_or_essential_trapped_blocker
        a b x y v hbd hstep hv M hM r heqx heqy
    refine ⟨m, hm, e, heq, hirr, hstrictRows, hmin, ?_, ?_⟩
    · rw [← hmin]
      exact heqEx
    · rcases hsplit with hbudget | hblock
      · have hmex : m - commonFaceDim a b x y = n - d := by
          rw [← hmin]
          exact heqEx
        omega
      · exact hblock

#print axioms rowCircuitStep_minPresentationExcess_le_ambient
#print axioms rowCircuitStep_same_phase_recursive_or_equalExcess_essential_trapped_blocker

end HirschCircuitLocalization
