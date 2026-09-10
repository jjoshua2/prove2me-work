import Mathlib
import Definitions.Def_Hirsch_model
import Theorems.Thm_Hirsch_nonzero_supporting_row_of_distinct_extremes
import Solutions.PolynomialTargetAccessDirectReduction
import Solutions.PolynomialTargetToPrescribed

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace Hirsch

/-- A polynomial diameter bound immediately gives polynomial access to some
supporting face of the target: walk all the way to the target and choose any
nonzero row supporting it. -/
theorem polynomial_target_face_access_of_polynomial_hirsch
    (hhirsch : ∃ c k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      (Hpoly a b).Nonempty → Bornology.IsBounded (Hpoly a b) →
      DiamLE (Hpoly a b) (c * (n + d) ^ k)) :
    ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hpoly a b) →
      ∀ u ∈ extremePoints ℝ (Hpoly a b),
      ∀ v ∈ extremePoints ℝ (Hpoly a b), u ≠ v →
      (∀ i, a i ≠ 0 → ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i) →
      ∃ (i : Fin n) (z : EuclideanSpace ℝ (Fin d)),
        a i ≠ 0 ∧ ⟪a i, v⟫ = b i ∧
        z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
        ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
          w 0 = u ∧ w (C * (n + d) ^ k) = z ∧
          ∀ j < C * (n + d) ^ k,
            w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  obtain ⟨c, k, hhirsch⟩ := hhirsch
  refine ⟨c, k, ?_⟩
  intro d n a b hbd u hu v hv huv _hsep
  obtain ⟨i, hai, hiv⟩ :=
    nonzero_supporting_row_of_distinct_extremes d n a b hbd u hu v hv huv
  have hD := hhirsch d n a b ⟨u, hu.1⟩ hbd
  obtain ⟨w, hw0, hwB, hwstep⟩ := hD u hu v hv
  exact ⟨i, v, hai, hiv, hv, hiv, w, hw0, hwB, hwstep⟩

/-- A polynomial diameter bound likewise gives access to every prescribed
nonzero supporting row of the target, with no loss in constants: again take
the endpoint itself. -/
theorem polynomial_prescribed_face_access_of_polynomial_hirsch
    (hhirsch : ∃ c k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      (Hpoly a b).Nonempty → Bornology.IsBounded (Hpoly a b) →
      DiamLE (Hpoly a b) (c * (n + d) ^ k)) :
    ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hpoly a b) →
      ∀ u ∈ extremePoints ℝ (Hpoly a b),
      ∀ v ∈ extremePoints ℝ (Hpoly a b), u ≠ v →
      (∀ j, a j ≠ 0 → ⟪a j, u⟫ ≠ b j ∨ ⟪a j, v⟫ ≠ b j) →
      ∀ i : Fin n, a i ≠ 0 → ⟪a i, v⟫ = b i →
      ∃ z : EuclideanSpace ℝ (Fin d),
        z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
        ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
          w 0 = u ∧ w (C * (n + d) ^ k) = z ∧
          ∀ j < C * (n + d) ^ k,
            w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  obtain ⟨c, k, hhirsch⟩ := hhirsch
  refine ⟨c, k, ?_⟩
  intro d n a b hbd u hu v hv _huv _hsep i _hai hiv
  have hD := hhirsch d n a b ⟨u, hu.1⟩ hbd
  obtain ⟨w, hw0, hwB, hwstep⟩ := hD u hu v hv
  exact ⟨v, hv, hiv, w, hw0, hwB, hwstep⟩

/-- Conversely, prescribed target-face access trivially implies existential
target-face access with the same constants by choosing one nonzero supporting
row of the target. -/
theorem polynomial_target_face_access_of_prescribed_face_access
    (hpres : ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hpoly a b) →
      ∀ u ∈ extremePoints ℝ (Hpoly a b),
      ∀ v ∈ extremePoints ℝ (Hpoly a b), u ≠ v →
      (∀ j, a j ≠ 0 → ⟪a j, u⟫ ≠ b j ∨ ⟪a j, v⟫ ≠ b j) →
      ∀ i : Fin n, a i ≠ 0 → ⟪a i, v⟫ = b i →
      ∃ z : EuclideanSpace ℝ (Fin d),
        z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
        ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
          w 0 = u ∧ w (C * (n + d) ^ k) = z ∧
          ∀ j < C * (n + d) ^ k,
            w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1))) :
    ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hpoly a b) →
      ∀ u ∈ extremePoints ℝ (Hpoly a b),
      ∀ v ∈ extremePoints ℝ (Hpoly a b), u ≠ v →
      (∀ i, a i ≠ 0 → ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i) →
      ∃ (i : Fin n) (z : EuclideanSpace ℝ (Fin d)),
        a i ≠ 0 ∧ ⟪a i, v⟫ = b i ∧
        z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
        ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
          w 0 = u ∧ w (C * (n + d) ^ k) = z ∧
          ∀ j < C * (n + d) ^ k,
            w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  obtain ⟨C, k, hpres⟩ := hpres
  refine ⟨C, k, ?_⟩
  intro d n a b hbd u hu v hv huv hsep
  obtain ⟨i, hai, hiv⟩ :=
    nonzero_supporting_row_of_distinct_extremes d n a b hbd u hu v hv huv
  obtain ⟨z, hz, hiz, w, hw0, hwB, hwstep⟩ :=
    hpres d n a b hbd u hu v hv huv hsep i hai hiv
  exact ⟨i, z, hai, hiv, hz, hiz, w, hw0, hwB, hwstep⟩

#print axioms nonzero_supporting_row_of_distinct_extremes
#print axioms polynomial_target_face_access_of_polynomial_hirsch
#print axioms polynomial_prescribed_face_access_of_polynomial_hirsch
#print axioms polynomial_target_face_access_of_prescribed_face_access
#print axioms polynomial_hirsch_of_target_face_access
#print axioms polynomial_prescribed_face_access_of_target_face_access

end Hirsch
