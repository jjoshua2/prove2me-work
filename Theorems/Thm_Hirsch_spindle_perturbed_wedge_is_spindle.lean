import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_wedge

open scoped RealInnerProductSpace

namespace Hirsch

/-- The perturbed dual wedge of a spindle, in standard position, is again a spindle.

Let $P\subseteq\mathbb R^d$ be a nonempty bounded H-polytope which is a spindle
with apices $\pm e_d$, and let inequality $i_0$ be tight at $+e_d$. Then there is
an inequality $i_1$ tight at $-e_d$ and a tilt $\varepsilon>0$ such that the
Klee--Walkup wedge of $P$ over $i_0$, with the $i_1$-facet tilted by $\varepsilon$
in the new coordinate, is a nonempty bounded $(d+1)$-spindle with $n+1$
inequalities, whose apices are the embeddings of $\pm e_d$ at height zero. -/
theorem spindle_perturbed_wedge_is_spindle (d n : ℕ) (hd : 0 < d) (hn : 2 * d < n)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (i0 : Fin n)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ) ∈
      Set.extremePoints ℝ (Hpoly a b))
    (hv : EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (-1 : ℝ) ∈
      Set.extremePoints ℝ (Hpoly a b))
    (hspindle : ∀ i,
      (⟪a i, EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ)⟫ = b i) ↔
        ⟪a i, EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (-1 : ℝ)⟫ ≠ b i)
    (htight : ⟪a i0, EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ)⟫ = b i0) :
    ∃ (i1 : Fin n) (ε : ℝ)
      (a' : Fin (n + 1) → EuclideanSpace ℝ (Fin (d + 1)))
      (b' : Fin (n + 1) → ℝ)
      (u' v' : EuclideanSpace ℝ (Fin (d + 1))),
      0 < ε ∧
      a' = perturbWedgeA a i0 i1 ε ∧
      b' = wedgeB b ∧
      u' = embed (EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ)) 0 ∧
      v' = embed (EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (-1 : ℝ)) 0 ∧
      (Hpoly a' b').Nonempty ∧
      Bornology.IsBounded (Hpoly a' b') ∧
      u' ∈ Set.extremePoints ℝ (Hpoly a' b') ∧
      v' ∈ Set.extremePoints ℝ (Hpoly a' b') ∧
      ∀ i, (⟪a' i, u'⟫ = b' i) ↔ ⟪a' i, v'⟫ ≠ b' i := by sorry

end Hirsch
