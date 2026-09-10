import Solutions.PolynomialHpolyHorizonKernel

/-! A genuinely new horizon vertex has a nonzero inward direction which
annihilates all old active rows, and at least one previously inactive old row
increases along that direction. -/

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section
namespace HirschHpolyCap

variable {d n : ℕ}

lemma exists_inward_old_active_direction
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (cappedHpoly a b T))
    (horizon : ⟪capNormal a, x⟫ = T)
    (hnotold : x ∉ extremePoints ℝ (Hpoly a b)) :
    ∃ r : EuclideanSpace ℝ (Fin d),
      r ≠ 0 ∧
      (∀ i, ⟪a i, x⟫ = b i → ⟪a i, r⟫ = 0) ∧
      ⟪capNormal a, r⟫ < 0 := by
  have hex : ∃ r : EuclideanSpace ℝ (Fin d),
      r ≠ 0 ∧ (∀ i, ⟪a i, x⟫ = b i → ⟪a i, r⟫ = 0) := by
    by_contra hnone
    have hsep : ∀ y : EuclideanSpace ℝ (Fin d),
        (∀ i, ⟪a i, x⟫ = b i → ⟪a i, y⟫ = 0) → y = 0 := by
      intro y hy
      by_contra hy0
      exact hnone ⟨y, hy0, hy⟩
    exact hnotold (extreme_of_tight_rows_separate a b x hx.1.1 hsep)
  obtain ⟨r, hr0, hr⟩ := hex
  have hcr0 : ⟪capNormal a, r⟫ ≠ 0 := by
    intro hz
    exact hr0 (horizon_active_rows_separate a b T x hx horizon r hr hz)
  by_cases hneg : ⟪capNormal a, r⟫ < 0
  · exact ⟨r, hr0, hr, hneg⟩
  · have hpos : 0 < ⟪capNormal a, r⟫ := lt_of_le_of_ne (le_of_not_gt hneg) hcr0.symm
    refine ⟨-r, neg_ne_zero.mpr hr0, ?_, ?_⟩
    · intro i hi
      rw [inner_neg_right, hr i hi, neg_zero]
    · rw [inner_neg_right]
      linarith

lemma inward_direction_has_increasing_old_row
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    {r : EuclideanSpace ℝ (Fin d)}
    (hin : ⟪capNormal a, r⟫ < 0) :
    ∃ i, 0 < ⟪a i, r⟫ := by
  by_contra h
  push Not at h
  have hr : RecessionDir a r := fun i => h i
  exact (not_lt_of_ge (capNormal_nonneg_on_recession a hr)) hin

lemma exists_increasing_inactive_row_at_new_horizon
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (cappedHpoly a b T))
    (horizon : ⟪capNormal a, x⟫ = T)
    (hnotold : x ∉ extremePoints ℝ (Hpoly a b)) :
    ∃ r : EuclideanSpace ℝ (Fin d), ∃ i : Fin n,
      r ≠ 0 ∧
      (∀ j, ⟪a j, x⟫ = b j → ⟪a j, r⟫ = 0) ∧
      ⟪capNormal a, r⟫ < 0 ∧
      0 < ⟪a i, r⟫ ∧
      ⟪a i, x⟫ < b i := by
  obtain ⟨r, hr0, hr, hcap⟩ :=
    exists_inward_old_active_direction a b T x hx horizon hnotold
  obtain ⟨i, hi⟩ := inward_direction_has_increasing_old_row a hcap
  have hix : ⟪a i, x⟫ < b i := by
    have hle := hx.1.1 i
    exact lt_of_le_of_ne hle (fun heq => (lt_irrefl 0) (by simpa [hr i heq] using hi))
  exact ⟨r, i, hr0, hr, hcap, hi, hix⟩

#print axioms exists_inward_old_active_direction
#print axioms inward_direction_has_increasing_old_row
#print axioms exists_increasing_inactive_row_at_new_horizon

end HirschHpolyCap
