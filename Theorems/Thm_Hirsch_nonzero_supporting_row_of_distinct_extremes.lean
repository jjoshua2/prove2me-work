import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch

theorem nonzero_supporting_row_of_distinct_extremes :
    ∀ (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hpoly a b) →
      ∀ u ∈ Set.extremePoints ℝ (Hpoly a b),
      ∀ v ∈ Set.extremePoints ℝ (Hpoly a b), u ≠ v →
      ∃ i : Fin n, a i ≠ 0 ∧ ⟪a i, v⟫ = b i := by sorry

end Hirsch
