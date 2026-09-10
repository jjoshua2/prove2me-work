import Solutions.PolynomialSimultaneousClipDiameter

/-! Public submission adapter for the CI-verified bounded simultaneous-clipping theorem. -/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

theorem solution
    {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : Set (EuclideanSpace ℝ (Fin d)))
    (hQc : IsCompact Q) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (D : ℕ) (B : ι → ℕ) (hD : DiamLE Q D)
    (hFaces : ∀ i,
      DiamLE ((Q ∩ {x | ∀ j, ⟪a j, x⟫ ≤ b j}) ∩ {z | ⟪a i, z⟫ = b i}) (B i)) :
    DiamLE (Q ∩ {x | ∀ i, ⟪a i, x⟫ ≤ b i}) (D + ∑ i, B i) := by
  exact HirschRadial.simultaneous_clipping_diameter_bound Q hQc hQ a b D B hD hFaces

#print axioms solution
