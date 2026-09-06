import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

/-- A spindle can be affinely moved so that its apices are $e_d$ and $-e_d$.

Let $P\subseteq\mathbb R^d$ be a nonempty bounded H-polytope that is a spindle
of length greater than $d$ with apices $u,v$. Then there is an affine
automorphism of $\mathbb R^d$ carrying $P$ to another such H-polytope $P'$
whose apices are the last standard basis vector and its negative, preserving
nonemptiness, boundedness, the spindle (XOR) property, and the absence of a
padded walk of length $d$ between the apices. -/
theorem spindle_normalize (d n : ℕ) (hd : 0 < d)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ Set.extremePoints ℝ (Hpoly a b))
    (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (hspindle : ∀ i, (⟪a i, u⟫ = b i) ↔ ⟪a i, v⟫ ≠ b i)
    (hlong : ∀ w : ℕ → EuclideanSpace ℝ (Fin d),
      ¬ (w 0 = u ∧ w d = v ∧
          ∀ j < d, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)))) :
    ∃ (a' : Fin n → EuclideanSpace ℝ (Fin d)) (b' : Fin n → ℝ),
      (Hpoly a' b').Nonempty ∧
      Bornology.IsBounded (Hpoly a' b') ∧
      EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ) ∈
        Set.extremePoints ℝ (Hpoly a' b') ∧
      EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (-1 : ℝ) ∈
        Set.extremePoints ℝ (Hpoly a' b') ∧
      (∀ i, (⟪a' i, EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ)⟫ = b' i) ↔
        ⟪a' i, EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (-1 : ℝ)⟫ ≠ b' i) ∧
      (∀ i, ⟪a i, u⟫ = b i ↔
        ⟪a' i, EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ)⟫ = b' i) ∧
      ∀ w : ℕ → EuclideanSpace ℝ (Fin d),
        ¬ (w 0 = EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ) ∧
            w d = EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (-1 : ℝ) ∧
            ∀ j < d, w j = w (j + 1) ∨ Adj (Hpoly a' b') (w j) (w (j + 1))) := by sorry

end Hirsch
