import Mathlib
import Definitions.Def_Hirsch_model
import Solutions.PolynomialCommonFace

open scoped RealInnerProductSpace
open Set Hirsch HirschPolynomialAccess

/-- Every vertex avoiding all nonzero target supporting rows shares with the
source an extreme face in an affine space of dimension at most `n - 2*d`.
The source and target must be separated extreme vertices. Boundedness is not
required. The statement uses only the published H-polytope model and Mathlib. -/
theorem solution
    (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i)
    (havoid : ∀ i, a i ≠ 0 →
      ⟪a i, v⟫ = b i → ⟪a i, x⟫ ≠ b i) :
    ∃ W : Submodule ℝ (EuclideanSpace ℝ (Fin d)),
      Module.finrank ℝ W ≤ n - 2 * d ∧
      x - u ∈ W ∧
      IsExtreme ℝ (Hpoly a b)
        {y | y ∈ Hpoly a b ∧ y - u ∈ W} := by
  refine ⟨commonDirection a b u x,
    common_direction_finrank_le_excess a b u v x hu hv hx hsep havoid, ?_, ?_⟩
  · exact ((mem_commonFace_iff_sub_mem_commonDirection a b u x x).mp
      (commonFace_x_mem a b u x hx.1)).2
  · have hset : {y | y ∈ Hpoly a b ∧ y - u ∈ commonDirection a b u x} =
        commonFace a b u x := by
      ext y
      exact (mem_commonFace_iff_sub_mem_commonDirection a b u x y).symm
    rw [hset]
    exact commonFace_isExtreme a b u x

#print axioms solution
