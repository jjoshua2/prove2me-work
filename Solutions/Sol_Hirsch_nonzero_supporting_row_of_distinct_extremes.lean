import Theorems.Thm_Hirsch_vertex_tight_rows_span

open scoped RealInnerProductSpace
open Hirsch

theorem solution :
    ∀ (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hpoly a b) →
      ∀ u ∈ Set.extremePoints ℝ (Hpoly a b),
      ∀ v ∈ Set.extremePoints ℝ (Hpoly a b), u ≠ v →
      ∃ i : Fin n, a i ≠ 0 ∧ ⟪a i, v⟫ = b i := by
  intro d n a b hbd u hu v hv huv
  by_contra hnone
  have hspan :
      ∀ j, ⟪a j, v⟫ = b j → ⟪a j, u - v⟫ = 0 := by
    intro j hj
    have haj : a j = 0 := by
      by_contra hne
      exact hnone ⟨j, hne, hj⟩
    simp [haj]
  have hzero := vertex_tight_rows_span d n a b v hv (u - v) hspan
  exact huv (sub_eq_zero.mp hzero)
