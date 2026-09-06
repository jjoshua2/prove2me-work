import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

theorem five_spindle_length_six :
    ∃ (n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin 5)) (b : Fin n → ℝ)
      (u v : EuclideanSpace ℝ (Fin 5)),
      25 ≤ n ∧
      (Hpoly a b).Nonempty ∧
      Bornology.IsBounded (Hpoly a b) ∧
      u ∈ Set.extremePoints ℝ (Hpoly a b) ∧
      v ∈ Set.extremePoints ℝ (Hpoly a b) ∧
      (∀ i, (⟪a i, u⟫ = b i) ↔ ⟪a i, v⟫ ≠ b i) ∧
      ∀ w : ℕ → EuclideanSpace ℝ (Fin 5),
        ¬ (w 0 = u ∧ w 5 = v ∧
            ∀ j < 5, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1))) := by sorry

end Hirsch
