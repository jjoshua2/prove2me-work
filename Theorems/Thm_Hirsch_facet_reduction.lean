import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

theorem facet_reduction (d k : ℕ) (a : Fin (k + 1) → EuclideanSpace ℝ (Fin d))
    (b : Fin (k + 1) → ℝ) (i : Fin (k + 1)) (hai : a i ≠ 0)
    (hbd : Bornology.IsBounded (Hpoly a b)) (B : ℕ)
    (IH : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin k → ℝ),
      Bornology.IsBounded (Hpoly a' b') → DiamLE (Hpoly a' b') B)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Set.extremePoints ℝ {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i})
    (hv : v ∈ Set.extremePoints ℝ {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i}) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = u ∧ w B = v ∧
      ∀ j < B, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by sorry

end Hirsch
