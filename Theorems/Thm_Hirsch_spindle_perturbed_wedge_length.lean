import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_wedge

open scoped RealInnerProductSpace

namespace Hirsch

/-- The perturbed dual wedge increases spindle length by at least one.

Let $P\subseteq\mathbb R^d$ be a $d$-spindle of length greater than $d$ with
apices $\pm e_d$, and let $P'$ be a perturbed dual wedge of $P$ as in
`spindle_perturbed_wedge_is_spindle`. Then $P'$ has no padded walk of length
$d+1$ between the images of the apices.

This is the length-increase half of Santos, Annals of Mathematics 176 (2012),
Theorem 2.6: after the one-point suspension, a generic vertical perturbation of
a vertex of the non-simplex base raises dual distance by one. -/
theorem spindle_perturbed_wedge_length (d n : ℕ) (hd : 0 < d) (hn : 2 * d < n)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (i0 i1 : Fin n) (ε : ℝ)
    (a' : Fin (n + 1) → EuclideanSpace ℝ (Fin (d + 1)))
    (b' : Fin (n + 1) → ℝ)
    (u' v' : EuclideanSpace ℝ (Fin (d + 1)))
    (hε : 0 < ε)
    (ha' : a' = perturbWedgeA a i0 i1 ε)
    (hb' : b' = wedgeB b)
    (hu' : u' = embed (EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ)) 0)
    (hv' : v' = embed (EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (-1 : ℝ)) 0)
    (hlong : ∀ w : ℕ → EuclideanSpace ℝ (Fin d),
      ¬ (w 0 = EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ) ∧
          w d = EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (-1 : ℝ) ∧
          ∀ j < d, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)))) :
    ∀ w : ℕ → EuclideanSpace ℝ (Fin (d + 1)),
      ¬ (w 0 = u' ∧ w (d + 1) = v' ∧
          ∀ j < d + 1, w j = w (j + 1) ∨
            Adj (Hpoly a' b') (w j) (w (j + 1))) := by sorry

end Hirsch
