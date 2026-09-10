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
      nlinarith
    rw [inner_sub_right, hip, hi, sub_self])
  exact sub_eq_zero.mp hpx

#print axioms extreme_of_tight_rows_separate

end HirschHpolyCap
