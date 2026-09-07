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
so this is exactly an elementary vector in its slack-direction space. -/
def IsRowCircuit {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d)) : Prop :=
  g ≠ 0 ∧ ∀ h : EuclideanSpace ℝ (Fin d), h ≠ 0 →
    circuitRowSupport a h ⊆ circuitRowSupport a g →
      circuitRowSupport a g ⊆ circuitRowSupport a h

/-- A maximal feasible circuit augmentation, normalized so the chosen step
length is one. The endpoints need NOT be vertices, and this is NOT `Adj`.
Positive rescaling of an elementary direction gives the usual definition. -/
def RowCircuitStep {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) : Prop :=
  x ∈ Hpoly a b ∧ y ∈ Hpoly a b ∧ IsRowCircuit a (y - x) ∧
    ∀ t : ℝ, 1 < t → x + t • (y - x) ∉ Hpoly a b

/-- A feasible padded circuit walk. Stationary steps are allowed, as in
`DiamLE`, but every point up to the budget is explicitly feasible. -/
def RowCircuitWalk {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (L : ℕ) (u v : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
    w 0 = u ∧ w L = v ∧
    (∀ j ≤ L, w j ∈ Hpoly a b) ∧
    ∀ j < L, w j = w (j + 1) ∨ RowCircuitStep a b (w j) (w (j + 1))

end Hirsch
