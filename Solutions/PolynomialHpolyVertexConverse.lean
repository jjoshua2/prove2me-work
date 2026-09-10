import Solutions.PolynomialHpolyFarCapPreserve

/-! Converse to the active-row spanning lemma: if the active H-rows at a
feasible point annihilate only the zero direction, then the point is extreme. -/

open scoped RealInnerProductSpace
open Set Hirsch

namespace HirschHpolyCap

variable {d n : ℕ}

lemma extreme_of_tight_rows_separate
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b)
    (hsep : ∀ y : EuclideanSpace ℝ (Fin d),
      (∀ i, ⟪a i, x⟫ = b i → ⟪a i, y⟫ = 0) → y = 0) :
    x ∈ extremePoints ℝ (Hpoly a b) := by
  refine ⟨hx, ?_⟩
  intro p hp q hq hop
  have hpx : p - x = 0 := hsep (p - x) (by
    intro i hi
    obtain ⟨α, β, hα, hβ, hab, hcomb⟩ := hop
    have hp_i := hp i
    have hq_i := hq i
    have hx_combo : ⟪a i, x⟫ = α * ⟪a i, p⟫ + β * ⟪a i, q⟫ := by
      rw [← hcomb, inner_add_right, inner_smul_right, inner_smul_right]
    have hip : ⟪a i, p⟫ = b i := by
      apply le_antisymm hp_i
      by_contra hnot
      have hp_lt : ⟪a i, p⟫ < b i := lt_of_not_ge hnot
      have hp_mul : α * ⟪a i, p⟫ < α * b i := mul_lt_mul_of_pos_left hp_lt hα
      have hq_mul : β * ⟪a i, q⟫ ≤ β * b i :=
        mul_le_mul_of_nonneg_left hq_i hβ.le
      have hsum : α * ⟪a i, p⟫ + β * ⟪a i, q⟫ < α * b i + β * b i :=
        add_lt_add_of_lt_of_le hp_mul hq_mul
      have hright : α * b i + β * b i = b i := by
        calc
          α * b i + β * b i = (α + β) * b i := by ring
          _ = b i := by rw [hab, one_mul]
      have hcontra : b i < b i := by
        calc
          b i = ⟪a i, x⟫ := hi.symm
          _ = α * ⟪a i, p⟫ + β * ⟪a i, q⟫ := hx_combo
          _ < α * b i + β * b i := hsum
          _ = b i := hright
      exact (lt_irrefl (b i)) hcontra
    rw [inner_sub_right, hip, hi, sub_self])
  exact sub_eq_zero.mp hpx

#print axioms extreme_of_tight_rows_separate

end HirschHpolyCap
