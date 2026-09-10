import Solutions.PolynomialSimultaneousClipDiameter

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

/-- Public-type wrapper for simultaneous clipping with all final vertices allowed.
The statement exposes only the outer set and the final halfspace intersection;
`HirschRadial.clipSet` is expanded from the public theorem type. -/
theorem solution
    {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQc : IsCompact Q) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (D : ℕ) (B : ι → ℕ) (hD : DiamLE Q D)
    (hFaces : ∀ i,
      DiamLE ((Q ∩ {x | ∀ j, ⟪a j, x⟫ ≤ b j}) ∩ {z | ⟪a i, z⟫ = b i}) (B i)) :
    DiamLE (Q ∩ {x | ∀ i, ⟪a i, x⟫ ≤ b i}) (D + ∑ i, B i) := by
  simpa [HirschRadial.clipSet] using
    (HirschRadial.simultaneous_clipping_diameter_bound Q hQc hQ a b D B hD hFaces)

#print axioms solution
