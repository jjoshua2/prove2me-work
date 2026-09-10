import Solutions.PolynomialHpolyExteriorCapTransfer

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

/-- Public-type wrapper for the canonical far-cap transfer on a finite
H-polyhedron.  The summed cap normal and simultaneous clip are expanded in the
statement so the theorem type uses only Mathlib and the public Hirsch model. -/
theorem solution
    {d n : ℕ} {ι : Type*} [Fintype ι]
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (f : ι → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (c : ι → ℝ)
    (T : ℝ)
    (hkernel : ∀ r : EuclideanSpace ℝ (Fin d),
      (∀ j, ⟪a j, r⟫ = 0) → r = 0)
    (D : ℕ) (hD : DiamLE (Hpoly a b) D)
    (hOldBelow : ∀ x ∈ extremePoints ℝ (Hpoly a b),
      ⟪-(∑ j, a j), x⟫ ≤ T)
    (hFinalBelow : ∀ x ∈ Hpoly a b ∩ {y | ∀ i, f i y ≤ c i},
      ⟪-(∑ j, a j), x⟫ < T)
    (B : ι → ℕ)
    (hB : ∀ i, DiamLE
      ((Hpoly a b ∩ {y | ∀ j, f j y ≤ c j}) ∩ {x | f i x = c i}) (B i)) :
    DiamLE (Hpoly a b ∩ {y | ∀ i, f i y ≤ c i}) (D + 1 + ∑ i, B i) := by
  have hOld : ∀ x ∈ extremePoints ℝ (Hpoly a b),
      ⟪HirschHpolyCap.capNormal a, x⟫ ≤ T := by
    simpa [HirschHpolyCap.capNormal] using hOldBelow
  have hFinal : ∀ x ∈ HirschRadial.finalClip (Hpoly a b) f c,
      ⟪HirschHpolyCap.capNormal a, x⟫ < T := by
    simpa [HirschRadial.finalClip, HirschHpolyCap.capNormal] using hFinalBelow
  have hFaces : ∀ i, DiamLE
      (HirschRadial.finalClip (Hpoly a b) f c ∩ {x | f i x = c i}) (B i) := by
    intro i
    simpa [HirschRadial.finalClip] using hB i
  have h := HirschHpolyCap.simultaneous_clip_diameter_from_finite_hpoly_far_cap
    a b f c T hkernel D hD hOld hFinal B hFaces
  simpa [HirschRadial.finalClip] using h

#print axioms solution
