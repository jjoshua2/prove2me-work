import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

theorem balanced_hpoly_transfer (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)) :
    ∃ (D : ℕ) (aQ : Fin (2 * D) → EuclideanSpace ℝ (Fin D)) (bQ : Fin (2 * D) → ℝ),
      D = d + (n - 2 * d) ∧
      (Hpoly aQ bQ).Nonempty ∧
      Bornology.IsBounded (Hpoly aQ bQ) ∧
      ∀ L : ℕ, DiamLE (Hpoly aQ bQ) L → DiamLE (Hpoly a b) L := by sorry

end Hirsch
