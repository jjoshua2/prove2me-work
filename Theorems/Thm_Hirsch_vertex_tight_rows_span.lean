import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch

theorem vertex_tight_rows_span (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (e : EuclideanSpace ℝ (Fin d)) (he : ∀ j, ⟪a j, v⟫ = b j → ⟪a j, e⟫ = 0) :
    e = 0 := by sorry

end Hirsch
