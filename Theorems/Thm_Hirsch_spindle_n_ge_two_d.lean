import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

/-- A spindle in dimension $d$ is described by at least $2d$ inequalities:
the two apices have disjoint tight sets, and each extreme point is cut out
by at least $d$ linearly independent inequalities. -/
theorem spindle_n_ge_two_d (d n : ℕ) (hd : 0 < d)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Set.extremePoints ℝ (Hpoly a b))
    (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (hspindle : ∀ i, (⟪a i, u⟫ = b i) ↔ ⟪a i, v⟫ ≠ b i) :
    2 * d ≤ n := by sorry

end Hirsch
