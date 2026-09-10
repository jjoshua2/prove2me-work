import Solutions.PolynomialExteriorCapNoStrict

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

/-- Public-type wrapper for the generic exterior-route clipping transfer with no
separately supplied strict centre. Exterior-region shortcuts are explicit in
the raw padded-walk hypothesis. -/
theorem solution
    {d : ℕ} {ι : Type*} [Fintype ι]
    (R G : Set (EuclideanSpace ℝ (Fin d)))
    (hR : Convex ℝ R) (hRc : IsCompact R)
    (hG : Convex ℝ G) (hGR : G ⊆ R)
    (f : ι → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (b : ι → ℝ)
    (hout : ∀ x ∈ G, x ∉ R ∩ {y | ∀ i, f i y ≤ b i})
    (D : ℕ)
    (hD : ∀ a ∈ extremePoints ℝ R, ∀ c ∈ extremePoints ℝ R,
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = a ∧ w D = c ∧
        ∀ k < D,
          w k = w (k + 1) ∨
            (Adj R (w k) (w (k + 1)) ∨ (w k ∈ G ∧ w (k + 1) ∈ G)))
    (B : ι → ℕ)
    (hB : ∀ i, DiamLE ((R ∩ {y | ∀ j, f j y ≤ b j}) ∩ {x | f i x = b i}) (B i)) :
    DiamLE (R ∩ {y | ∀ i, f i y ≤ b i}) (D + ∑ i, B i) := by
  exact HirschExterior.clip_diameter_from_exterior_routes_no_strict
    R G hR hRc hG hGR f b hout D hD B hB

#print axioms solution
