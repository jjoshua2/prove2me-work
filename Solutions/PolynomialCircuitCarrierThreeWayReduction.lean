import Mathlib
import Solutions.PolynomialCircuitIrredundantMinCarrierDichotomy
import Solutions.PolynomialLowerExcessCarrierRecursion
import Solutions.PolynomialCommonFaceRowBlockRouting

open scoped BigOperators RealInnerProductSpace
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- Structural certificate that a minimum equivalent row presentation of the
common carrier becomes a Cartesian product of independent row blocks after an
invertible linear coordinate change, with every block having row excess at
most three.

The total minimum presentation excess may be arbitrarily large. -/
def CommonFaceMinPresentationHasSmallRowBlocks
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ e : Fin (commonFaceMinSubpresentationCount a b u v) ↪ Fin n,
    Hpoly
        (fun j => commonFaceA a b u v (e j))
        (fun j => commonFaceB a b u v (e j)) =
      Hpoly (commonFaceA a b u v) (commonFaceB a b u v) ∧
    ∃ k : ℕ,
      ∃ dims counts : Fin k → ℕ,
      ∃ T : EuclideanSpace ℝ (Fin (commonFaceDim a b u v)) ≃ₗ[ℝ]
          (∀ i : Fin k, EuclideanSpace ℝ (Fin (dims i))),
      ∃ rowEquiv :
          (Σ i : Fin k, Fin (counts i)) ≃
            Fin (commonFaceMinSubpresentationCount a b u v),
      ∃ A : ∀ i : Fin k, Fin (counts i) → EuclideanSpace ℝ (Fin (dims i)),
        (∀ z i j,
          ⟪commonFaceA a b u v (e (rowEquiv ⟨i, j⟩)), T.symm z⟫ =
            ⟪A i j, z i⟫) ∧
        (∀ i, dims i ≤ counts i) ∧
        (∀ i, counts i ≤ dims i + 3)

/-- The ordered certificate left by a saturated, non-factorized same-phase
row-circuit carrier: an irredundant strictly feasible minimum carrier model has
an indispensable row which is target-only for the local step, strictly slack at
the final target, already trapped at the phase reference, and newly blocking at
the step endpoint. The final point `q` certifies indispensability by making this
row uniquely tight in the minimum model. -/
def CommonFaceHasEssentialTrappedBlocker
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

/-- Three-way reduction for a same-phase maximal row-circuit step.

Assume a uniform diameter bound `B` for all bounded H-polyhedra of strictly
smaller row excess than the ambient `n-d`, and the already-proved small-excess
base through excess three. Then every step carrier is in one of three classes:

1. its minimum presentation excess is strictly smaller than `n-d`, hence the
   carrier is solved by the lower-excess induction hypothesis with cost `B`;
2. a minimum presentation factorizes into independent blocks of excess at most
   three, hence the carrier is solved directly with exact cost `M_min-h` even if
   that excess is large;
3. the minimum carrier is not so factorable, and it carries the indispensable
   trapped-blocker certificate above.

Thus the unresolved equality case is narrowed to genuinely coupled saturated
minimum carriers, not all high-excess carriers. -/
theorem rowCircuitStep_same_phase_recursive_or_factorized_or_essential_trapped_blocker
    (hsmall : SmallExcessHpolyBound)
    {d n B : ℕ}
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
    DiamLE (commonFace a b x y)
      (commonFaceMinSubpresentationCount a b x y - commonFaceDim a b x y) ∨
    (¬ CommonFaceMinPresentationHasSmallRowBlocks a b x y ∧
      CommonFaceHasEssentialTrappedBlocker a b x y v M r) := by
  classical
  by_cases hblocks : CommonFaceMinPresentationHasSmallRowBlocks a b x y
  · right
    left
    rcases hblocks with
      ⟨e, heq, k, dims, counts, T, rowEquiv, A, hrows, hcount, hsmallcount⟩
    exact commonFace_diamLE_minPresentationExcess_of_small_row_blocks
      hsmall a b x y hbd hstep.1 e heq dims counts T rowEquiv A
      hrows hcount hsmallcount
  · obtain ⟨m, hm, e, heq, hirr, hstrictRows, hmin, hcase⟩ :=
      rowCircuitStep_irredundant_minPresentation_same_phase_strict_budget_or_essential_trapped_blocker
        a b x y v hbd hstep hv M hM r heqx heqy
    rcases hcase with hbudget | hblocker
    · left
      have hex :
          commonFaceMinSubpresentationCount a b x y - commonFaceDim a b x y < n - d := by
        rw [hmin]
        omega
      exact commonFace_diamLE_of_minPresentationExcess_lt
        hIH a b x y hbd hstep.1 hex
    · right
      right
      exact ⟨hblocks, m, hm, e, heq, hirr, hstrictRows, hmin, hblocker⟩

#print axioms CommonFaceMinPresentationHasSmallRowBlocks
#print axioms CommonFaceHasEssentialTrappedBlocker
#print axioms rowCircuitStep_same_phase_recursive_or_factorized_or_essential_trapped_blocker

end HirschCircuitLocalization
