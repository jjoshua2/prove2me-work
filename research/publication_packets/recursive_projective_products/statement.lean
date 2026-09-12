import Mathlib
import Definitions.Def_Hirsch_recursive_projective_products
open Set Hirsch
open scoped RealInnerProductSpace
theorem Hirsch.hpoly_diameter_le_excess_of_recursive_projective_products {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (cert : HirschRecursiveProducts.ProductTree a b) : DiamLE (Hpoly a b) (n-d) := by sorry
