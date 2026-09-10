import Mathlib
import Solutions.CircuitEdgeBalancedReduction
import Solutions.PolynomialBalancedRowFaceCover
import Solutions.PolynomialProductWalk

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section

namespace HirschBalancedFaceCover

/-- Qualitative connectivity needed by the row-face averaging argument.
This is separated from the new quantitative hypothesis because general
bounded-polytope graph connectivity is already a proved result. -/
def BalancedGraphConnectivityClaim : Prop :=
  ∀ (D : ℕ)
    (a : Fin (2 * D) → EuclideanSpace ℝ (Fin D))
    (b : Fin (2 * D) → ℝ),
    (Hpoly a b).Nonempty → Bornology.IsBounded (Hpoly a b) →
    ∀ u ∈ extremePoints ℝ (Hpoly a b),
      ∀ v ∈ extremePoints ℝ (Hpoly a b),
        ∃ L, HirschFaceSplice.Walk (Hpoly a b) L u v

/-- Aggregate row-face hypothesis for balanced H-polytopes.

Unlike a uniform recursive facet bound, this asks only that the SUM of
intrinsic row-face budgets be polynomial after the natural multiplicity-`D`
normalization. A few difficult row faces are therefore allowed, provided the
whole family has polynomial aggregate cost. -/
def BalancedAggregateRowFaceClaim : Prop :=
  ∃ C k : ℕ, ∀ (D : ℕ)
    (a : Fin (2 * D) → EuclideanSpace ℝ (Fin D))
    (b : Fin (2 * D) → ℝ),
    (Hpoly a b).Nonempty → Bornology.IsBounded (Hpoly a b) →
    ∃ B : Fin (2 * D) → ℕ,
      (∀ i, DiamLE (nonzeroRowFace a b i) (B i)) ∧
      (∑ i, (B i + 1)) ≤ D * (C * D ^ k + 1)

/-- The balanced/d-step polynomial-diameter core follows from a polynomial
aggregate bound on the `2D` row supporting faces.

The key gain is the factor `D`: every vertex belongs to at least `D` nonzero
row faces, so shortest-path incidence counting divides the sum of face costs
by `D`. Thus one need not prove a comparable polynomial bound for every facet
separately. -/
theorem balanced_polynomial_of_aggregate_row_faces
    (hconnect : BalancedGraphConnectivityClaim)
    (hagg : BalancedAggregateRowFaceClaim) :
    HirschCircuit.BalancedPolynomialBoundClaim := by
  obtain ⟨C, k, hagg⟩ := hagg
  refine ⟨C, k, ?_⟩
  intro D a b hne hbd
  by_cases hD0 : D = 0
  · subst D
    intro u hu v hv
    have huv : u = v := Subsingleton.elim _ _
    subst v
    exact ⟨fun _ => u, rfl, rfl, fun _ _ => Or.inl rfl⟩
  · have hDpos : 0 < D := Nat.pos_of_ne_zero hD0
    obtain ⟨B, hFD, hsum⟩ := hagg D a b hne hbd
    have hparent :
        DiamLE (Hpoly a b) ((∑ i, (B i + 1)) / D - 1) :=
      balanced_diamLE_of_row_face_bounds D hDpos a b B hFD
        (hconnect D a b hne hbd)
    have hdiv : (∑ i, (B i + 1)) / D ≤ C * D ^ k + 1 := by
      exact Nat.div_le_of_le_mul hsum
    have hbudget : (∑ i, (B i + 1)) / D - 1 ≤ C * D ^ k := by
      omega
    intro u hu v hv
    obtain ⟨w, hw0, hwB, hwstep⟩ := hparent u hu v hv
    exact HirschProduct.pad_walk (Adj (Hpoly a b)) hbudget
      w hw0 hwB hwstep

#print axioms balanced_polynomial_of_aggregate_row_faces

end HirschBalancedFaceCover
