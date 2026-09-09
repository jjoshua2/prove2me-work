import Solutions.PolynomialExteriorCapClipping

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

/-- Public-type offline wrapper. The structural exterior cap and strict centre
are explicit hypotheses; this is not the unrestricted pointed H-polyhedron
existence/classification theorem. -/
theorem solution
    {d : ℕ} {ι : Type*} [Fintype ι]
    (R G V : Set (EuclideanSpace ℝ (Fin d)))
    (hR : Convex ℝ R) (hRc : IsCompact R)
    (hG : Convex ℝ G) (hGR : G ⊆ R)
    (f : ι → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (b : ι → ℝ)
    (o : EuclideanSpace ℝ (Fin d)) (ho : o ∈ R) (hs : ∀ i, f i o < b i)
    (hout : ∀ x ∈ G, x ∉ R ∩ {y | ∀ i, f i y ≤ b i})
    (D : ℕ)
    (hOld : ∀ a ∈ V, ∀ c ∈ V,
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = a ∧ w D = c ∧
        ∀ k < D, w k = w (k + 1) ∨ Adj R (w k) (w (k + 1)))
    (hclass : ∀ x ∈ extremePoints ℝ R,
      x ∈ V ∨ (x ∈ G ∧ ∃ a ∈ V, Adj R a x))
    (B : ι → ℕ)
    (hB : ∀ i, DiamLE ((R ∩ {y | ∀ j, f j y ≤ b j}) ∩ {x | f i x = b i}) (B i)) :
    DiamLE (R ∩ {y | ∀ i, f i y ≤ b i}) (D + 1 + ∑ i, B i) := by
  exact HirschExterior.simultaneous_clip_diameter_from_exterior_cap
    R G V hR hRc hG hGR f b o ho hs hout D hOld hclass B hB

#print axioms solution
