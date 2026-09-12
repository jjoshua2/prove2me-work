import Mathlib
import Definitions.Def_Hirsch_model
open scoped RealInnerProductSpace
open Set Hirsch
namespace Hirsch
theorem hpoly_diameter_le_fixed_excess_larman
    (E d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hrows : n ≤ d + E) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (2 * E * 2 ^ (E - 3)) := by sorry
end Hirsch