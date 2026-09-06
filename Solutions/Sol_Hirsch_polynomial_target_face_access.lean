import Theorems.Thm_Hirsch_nonzero_supporting_row_of_distinct_extremes
import Theorems.Thm_Hirsch_polynomial_access_to_given_supporting_face

open scoped RealInnerProductSpace
open Hirsch

theorem solution :
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
            w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  obtain ⟨C, k, hcore⟩ := polynomial_access_to_given_supporting_face
  refine ⟨C, k, ?_⟩
  intro d n a b hbd u hu v hv huv hsep
  obtain ⟨i, hai, hiv⟩ :=
    nonzero_supporting_row_of_distinct_extremes d n a b hbd u hu v hv huv
  obtain ⟨z, hz, hiz, w, hw0, hwz, hwalk⟩ :=
    hcore d n a b hbd u hu v hv huv hsep i hai hiv
  exact ⟨i, z, hai, hiv, hz, hiz, w, hw0, hwz, hwalk⟩
