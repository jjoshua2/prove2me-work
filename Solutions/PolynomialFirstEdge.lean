import Mathlib
import Definitions.Def_Hirsch_model
import Theorems.Thm_Hirsch_vertex_tight_rows_span
import Solutions.PolynomialBalancedOneStep

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 1500000

noncomputable section

namespace HirschPolynomialAccess

variable {d n : ℕ}

/-- A genuine edge leaving an extreme point must acquire some nonzero tight
row that was not tight at the starting vertex.  Otherwise the new vertex's
tight normals, which span the ambient space, would annihilate `z-u` and force
`z=u`. -/
lemma adjacent_acquires_new_nonzero_row
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {u z : EuclideanSpace ℝ (Fin d)}
    (huz : Adj (Hpoly a b) u z) :
    ∃ i : Fin n,
      a i ≠ 0 ∧ ⟪a i, z⟫ = b i ∧ ⟪a i, u⟫ ≠ b i := by
  have hz : z ∈ extremePoints ℝ (Hpoly a b) :=
    adj_right_extreme (Hpoly a b) huz
  by_contra h
  push Not at h
  have horth : ∀ j, ⟪a j, z⟫ = b j → ⟪a j, z - u⟫ = 0 := by
    intro j hjz
    by_cases haj : a j = 0
    · simp [haj]
    · have hju : ⟪a j, u⟫ = b j := by
        by_contra hju
        exact h j haj hjz hju
      simp [inner_sub_right, hjz, hju]
  have hzero := Hirsch.vertex_tight_rows_span d n a b z hz (z - u) horth
  have hzu : z = u := sub_eq_zero.mp hzero
  exact huz.1 hzu.symm

/-- Under the separation hypothesis, the new row acquired by the first edge
is either already a target facet (success) or is neutral: tight at neither
original endpoint before the move. -/
lemma adjacent_hits_target_or_neutral
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v z : EuclideanSpace ℝ (Fin d))
    (hsep : ∀ j, a j ≠ 0 →
      ⟪a j, u⟫ ≠ b j ∨ ⟪a j, v⟫ ≠ b j)
    (huz : Adj (Hpoly a b) u z) :
    (∃ i : Fin n, a i ≠ 0 ∧ ⟪a i, v⟫ = b i ∧ ⟪a i, z⟫ = b i) ∨
    (∃ i : Fin n, a i ≠ 0 ∧
      ⟪a i, u⟫ ≠ b i ∧ ⟪a i, v⟫ ≠ b i ∧ ⟪a i, z⟫ = b i) := by
  obtain ⟨i, hai, hiz, hiu⟩ := adjacent_acquires_new_nonzero_row a b huz
  by_cases hiv : ⟪a i, v⟫ = b i
  · exact Or.inl ⟨i, hai, hiv, hiz⟩
  · exact Or.inr ⟨i, hai, hiu, hiv, hiz⟩

end HirschPolynomialAccess
