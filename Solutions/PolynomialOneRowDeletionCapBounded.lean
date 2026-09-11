import Mathlib
import Solutions.PolynomialOneRowDeletionCapFunctional

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschDeletion

/-- The capped one-row-deletion outer system: keep every row except `j`, and
add the explicit negative-row-sum cap `deletionCapValue <= M`. -/
def deletionCappedOuter
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (j : Fin n) (M : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | (∀ i : Fin n, i ≠ j → ⟪a i, x⟫ ≤ b i) ∧
    deletionCapValue a j x ≤ M}

/-- If the remaining-row evaluation map is injective, every finite level of the
explicit negative-row-sum cap makes the deletion outer bounded.

The proof is purely algebraic/topological. Original inequalities bound every
remaining row evaluation from above. The cap bound on the negative sum gives a
lower bound on each individual row evaluation once the other upper bounds are
inserted. Thus the remaining-row map sends the capped outer into a bounded
coordinate box. In finite dimension an injective linear map is anti-Lipschitz,
so boundedness pulls back from that box to the capped outer.

No vertex enumeration, recession-ray classification, irredundancy, or strict
feasibility is used. -/
theorem deletionCappedOuter_isBounded_of_injective
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (j : Fin n) (M : ℝ)
    (hinj : Function.Injective (rowMapWithout a j)) :
    Bornology.IsBounded (deletionCappedOuter a b j M) := by
  classical
  let I := {i : Fin n // i ≠ j}
  let upper : I → ℝ := fun i => b i.1
  let lower : I → ℝ := fun i =>
    (∑ k ∈ (Finset.univ.erase i), (-b k.1)) - M
  obtain ⟨K, hK, hanti⟩ :=
    (LinearMap.injective_iff_antilipschitz (rowMapWithout a j)).mp hinj
  have hbox : Bornology.IsBounded (Set.Icc lower upper) :=
    Metric.isBounded_Icc lower upper
  have hpre : Bornology.IsBounded ((rowMapWithout a j) ⁻¹' Set.Icc lower upper) :=
    hanti.isBounded_preimage hbox
  apply hpre.subset
  intro x hx
  change rowMapWithout a j x ∈ Set.Icc lower upper
  constructor
  · intro i
    have hupper : ∀ k : I, ⟪a k.1, x⟫ ≤ b k.1 := by
      intro k
      exact hx.1 k.1 k.2
    have hothers :
        (∑ k ∈ (Finset.univ.erase i), (-b k.1)) ≤
          ∑ k ∈ (Finset.univ.erase i), (-⟪a k.1, x⟫) := by
      apply Finset.sum_le_sum
      intro k hk
      exact neg_le_neg (hupper k)
    have hsplit :
        (∑ k ∈ (Finset.univ.erase i), (-⟪a k.1, x⟫)) +
            (-⟪a i.1, x⟫) = deletionCapValue a j x := by
      unfold deletionCapValue
      exact Finset.sum_erase_add _ _ (Finset.mem_univ i)
    have hcap := hx.2
    have htotal :
        (∑ k ∈ (Finset.univ.erase i), (-b k.1)) +
            (-⟪a i.1, x⟫) ≤ M := by
      calc
        (∑ k ∈ (Finset.univ.erase i), (-b k.1)) + (-⟪a i.1, x⟫) ≤
            (∑ k ∈ (Finset.univ.erase i), (-⟪a k.1, x⟫)) +
              (-⟪a i.1, x⟫) := by
                simpa [add_comm] using
                  (add_le_add_right hothers (-⟪a i.1, x⟫))
        _ = deletionCapValue a j x := hsplit
        _ ≤ M := hcap
    change (∑ k ∈ (Finset.univ.erase i), (-b k.1)) - M ≤ ⟪a i.1, x⟫
    linarith
  · intro i
    change rowMapWithout a j x i ≤ upper i
    simpa [rowMapWithout, upper] using hx.1 i.1 i.2

/-- Every cap level of every one-row deletion outer from a nonempty bounded
H-presentation is bounded. This combines the previous one-row pointedness
result with the algebraic cap-boundedness theorem above.

For the exterior-cap program this removes the compactness obstruction entirely:
choosing the cap level sufficiently far is needed only to preserve the desired
old vertices/final polytope and to obtain the cap-vertex classification, not to
make the truncation bounded. -/
theorem deletionCappedOuter_isBounded_of_bounded_parent
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b)
    (j : Fin n) (M : ℝ) :
    Bornology.IsBounded (deletionCappedOuter a b j M) := by
  exact deletionCappedOuter_isBounded_of_injective a b j M
    (rowMapWithout_injective_of_bounded a b hbd x hx j)

#print axioms deletionCappedOuter_isBounded_of_injective
#print axioms deletionCappedOuter_isBounded_of_bounded_parent

end HirschDeletion
