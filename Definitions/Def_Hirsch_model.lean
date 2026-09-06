import Mathlib

open scoped RealInnerProductSpace

namespace Hirsch

/-- The **H-polytope** cut out in $\mathbb{R}^d$ by the `n` linear inequalities
$\langle a_i, x\rangle \le b_i$: the set of points satisfying every inequality.
Boundedness and nonemptiness are not part of the definition; theorems assume
them explicitly. -/
def Hpoly {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, ⟪a i, x⟫ ≤ b i}

/-- Two points `u ≠ v` are **adjacent** on `P` when the segment `[u, v]` is an
extreme subset of `P`. For a polytope the convex extreme subsets are exactly
the faces, so this says `[u, v]` is a face of dimension one — an **edge** —
and its endpoints are then vertices (extreme points) of `P`. -/
def Adj {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) (u v : E) : Prop :=
  u ≠ v ∧ IsExtreme ℝ P (segment ℝ u v)

/-- `DiamLE P B`: every two vertices (extreme points) of `P` are joined by a
walk of `B` steps in the vertex-edge graph of `P`, where each step either
stays put or crosses an edge. Stationary steps make the predicate monotone in
`B`, so this says exactly that the combinatorial diameter of the graph of `P`
is at most `B` (and in particular that the graph is connected). -/
def DiamLE {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) (B : ℕ) : Prop :=
  ∀ u ∈ Set.extremePoints ℝ P, ∀ v ∈ Set.extremePoints ℝ P,
    ∃ w : ℕ → E, w 0 = u ∧ w B = v ∧
      ∀ i < B, w i = w (i + 1) ∨ Adj P (w i) (w (i + 1))

end Hirsch
