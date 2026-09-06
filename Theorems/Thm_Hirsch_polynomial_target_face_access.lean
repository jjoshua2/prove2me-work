import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch

theorem polynomial_target_face_access :
    ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hpoly a b) →
      ∀ u ∈ Set.extremePoints ℝ (Hpoly a b),
      ∀ v ∈ Set.extremePoints ℝ (Hpoly a b), u ≠ v →
      (∀ i, a i ≠ 0 → ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i) →
      ∃ (i : Fin n) (z : EuclideanSpace ℝ (Fin d)),
        a i ≠ 0 ∧ ⟪a i, v⟫ = b i ∧
        z ∈ Set.extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
        ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
          w 0 = u ∧ w (C * (n + d) ^ k) = z ∧
          ∀ j < C * (n + d) ^ k,
            w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by sorry

end Hirsch
