import Definitions.Def_Hirsch_model

set_option autoImplicit false
open scoped RealInnerProductSpace

namespace Hirsch

/-- Support of the change in describing inequalities along a direction.
These are row supports, not supports of the ambient coordinates. -/
def circuitRowSupport {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d)) : Set (Fin n) :=
  {i | ⟪a i, g⟫ ≠ 0}

/-- A nonzero direction whose row support is inclusion-minimal among all
nonzero directions. For a nonempty bounded H-polytope the row map is injective,
so this corresponds to an elementary vector in its slack-direction space. -/
def IsRowCircuit {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d)) : Prop :=
  g ≠ 0 ∧ ∀ h : EuclideanSpace ℝ (Fin d), h ≠ 0 →
    circuitRowSupport a h ⊆ circuitRowSupport a g →
      circuitRowSupport a g ⊆ circuitRowSupport a h

/-- A maximal feasible circuit augmentation, normalized to step length one.
Its endpoints need NOT be vertices. This relation is NOT `Adj`. -/
def RowCircuitStep {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) : Prop :=
  x ∈ Hpoly a b ∧ y ∈ Hpoly a b ∧ IsRowCircuit a (y - x) ∧
    ∀ t : ℝ, 1 < t → x + t • (y - x) ∉ Hpoly a b

/-- A feasible padded circuit walk. Every point up to the budget is feasible,
but intermediate points need not be extreme. -/
def RowCircuitWalk {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (L : ℕ) (u v : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
    w 0 = u ∧ w L = v ∧
    (∀ j ≤ L, w j ∈ Hpoly a b) ∧
    ∀ j < L, w j = w (j + 1) ∨ RowCircuitStep a b (w j) (w (j + 1))

/-- Deleting any row strictly enlarges the feasible set. This rules out
manufacturing extra circuit directions by adding redundant inequalities. -/
def RowPresentationIrredundant {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, ∃ x : EuclideanSpace ℝ (Fin d),
    (∀ j : Fin n, j ≠ i → ⟪a j, x⟫ ≤ b j) ∧ b i < ⟪a i, x⟫

/-- A strict feasible point for every row of the presentation. -/
def StrictlyFeasibleRows {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) : Prop :=
  ∃ x : EuclideanSpace ℝ (Fin d), ∀ i : Fin n, ⟪a i, x⟫ < b i

end Hirsch
