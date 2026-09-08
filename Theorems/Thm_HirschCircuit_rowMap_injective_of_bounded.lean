import Definitions.Def_Hirsch_circuit_slack_model

set_option autoImplicit false
open scoped RealInnerProductSpace
open Hirsch

namespace HirschCircuit

/-- A nonempty bounded H-polytope has no nonzero direction annihilated by every
row. Equivalently, its row-evaluation map is injective. -/
theorem rowMap_injective_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hb : Bornology.IsBounded (Hpoly a b))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b) :
    Function.Injective (rowMap a) := by sorry

end HirschCircuit
