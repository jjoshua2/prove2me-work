import Mathlib
import Solutions.PolynomialCompactCapVertexClassification
import Definitions.Def_Hirsch_circuit_slack_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschPointed

variable {d n : ℕ}

/-- Explicit coercive linear functional for an injective finite H-presentation. -/
def injectiveCapValue
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i : Fin n, (-⟪a i, x⟫)

/-- Euclidean normal representing `injectiveCapValue`. -/
def injectiveCapNormal
    (a : Fin n → EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  - ∑ i : Fin n, a i

lemma injectiveCapNormal_eval
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) :
    ⟪injectiveCapNormal a, x⟫ = injectiveCapValue a x := by
  simp [injectiveCapNormal, injectiveCapValue, sum_inner, Finset.sum_neg_distrib]

/-- Add the explicit negative-row-sum cap to an H-polyhedron. -/
def injectiveCappedHpoly
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (M : ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | x ∈ Hpoly a b ∧ injectiveCapValue a x ≤ M}

lemma injectiveCappedHpoly_eq_inter
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (M : ℝ) :
    injectiveCappedHpoly a b M =
      Hpoly a b ∩ {x | ⟪injectiveCapNormal a, x⟫ ≤ M} := by
  ext x
  simp only [injectiveCappedHpoly, mem_setOf_eq, mem_inter_iff]
  rw [injectiveCapNormal_eval]

/-- Injectivity of the row-evaluation map makes every finite level of the
negative-row-sum cap bounded.  No boundedness of the original H-polyhedron is
needed. -/
theorem injectiveCappedHpoly_isBounded
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (M : ℝ)
    (hinj : Function.Injective (HirschCircuit.rowMap a)) :
    Bornology.IsBounded (injectiveCappedHpoly a b M) := by
  classical
  let upper : Fin n → ℝ := b
  let lower : Fin n → ℝ := fun i =>
    (∑ k ∈ (Finset.univ.erase i), (-b k)) - M
  obtain ⟨K, hK, hanti⟩ :=
    (LinearMap.injective_iff_antilipschitz (HirschCircuit.rowMap a)).mp hinj
  have hbox : Bornology.IsBounded (Set.Icc lower upper) :=
    Metric.isBounded_Icc lower upper
  have hpre : Bornology.IsBounded
      ((HirschCircuit.rowMap a) ⁻¹' Set.Icc lower upper) :=
    hanti.isBounded_preimage hbox
  apply hpre.subset
  intro x hx
  change HirschCircuit.rowMap a x ∈ Set.Icc lower upper
  constructor
  · intro i
    have hupper : ∀ k : Fin n, ⟪a k, x⟫ ≤ b k := hx.1
    have hothers :
        (∑ k ∈ (Finset.univ.erase i), (-b k)) ≤
          ∑ k ∈ (Finset.univ.erase i), (-⟪a k, x⟫) := by
      apply Finset.sum_le_sum
      intro k hk
      exact neg_le_neg (hupper k)
    have hsplit :
        (∑ k ∈ (Finset.univ.erase i), (-⟪a k, x⟫)) +
            (-⟪a i, x⟫) = injectiveCapValue a x := by
      unfold injectiveCapValue
      exact Finset.sum_erase_add _ _ (Finset.mem_univ i)
    have htotal :
        (∑ k ∈ (Finset.univ.erase i), (-b k)) + (-⟪a i, x⟫) ≤ M := by
      calc
        (∑ k ∈ (Finset.univ.erase i), (-b k)) + (-⟪a i, x⟫) ≤
            (∑ k ∈ (Finset.univ.erase i), (-⟪a k, x⟫)) + (-⟪a i, x⟫) := by
              simpa [add_comm] using add_le_add_right hothers (-⟪a i, x⟫)
        _ = injectiveCapValue a x := hsplit
        _ ≤ M := hx.2
    change (∑ k ∈ (Finset.univ.erase i), (-b k)) - M ≤ ⟪a i, x⟫
    linarith
  · intro i
    change HirschCircuit.rowMap a x i ≤ upper i
    simpa [HirschCircuit.rowMap, upper] using hx.1 i

/-- Every nonempty finite H-polyhedron with injective row map has an original
vertex, even when it is unbounded.

Proof: cap it by the explicit negative row sum at any feasible finite level.
The cap is nonempty and compact.  Choose a capped vertex.  The verified compact
single-cut classification says it is either already an old vertex or is
adjacent to an old vertex; either alternative produces an original vertex. -/
theorem hpoly_extremePoints_nonempty_of_rowMap_injective
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty)
    (hinj : Function.Injective (HirschCircuit.rowMap a)) :
    (extremePoints ℝ (Hpoly a b)).Nonempty := by
  classical
  obtain ⟨x, hx⟩ := hne
  let c := injectiveCapNormal a
  let M := injectiveCapValue a x
  let R := injectiveCappedHpoly a b M
  have hRne : R.Nonempty := by
    refine ⟨x, hx, ?_⟩
    exact le_rfl
  have hRbd : Bornology.IsBounded R :=
    injectiveCappedHpoly_isBounded a b M hinj
  have hRc : IsClosed R := by
    change IsClosed (injectiveCappedHpoly a b M)
    rw [injectiveCappedHpoly_eq_inter]
    exact (HirschCapVertices.hpoly_isClosed a b).inter
      (isClosed_le (by fun_prop) continuous_const)
  have hRcompact : IsCompact R :=
    Metric.isCompact_iff_isClosed_bounded.2 ⟨hRc, hRbd⟩
  obtain ⟨z, hz⟩ := hRcompact.extremePoints_nonempty hRne
  have hmodel :
      R = Hpoly a b ∩ {y | ⟪c, y⟫ ≤ M} := by
    simpa [c] using injectiveCappedHpoly_eq_inter a b M
  have hcompactModel : IsCompact (Hpoly a b ∩ {y | ⟪c, y⟫ ≤ M}) := by
    rw [← hmodel]
    exact hRcompact
  have hzModel : z ∈ extremePoints ℝ (Hpoly a b ∩ {y | ⟪c, y⟫ ≤ M}) := by
    rw [← hmodel]
    exact hz
  rcases HirschCapVertices.compact_hpoly_cap_vertex_classification
      a b c M hcompactModel z hzModel with hold | hnew
  · exact ⟨z, hold⟩
  · obtain ⟨_hzcap, v, hv, _hvbelow, _hAdj⟩ := hnew
    exact ⟨v, hv⟩

#print axioms injectiveCapNormal_eval
#print axioms injectiveCappedHpoly_isBounded
#print axioms hpoly_extremePoints_nonempty_of_rowMap_injective

end HirschPointed
