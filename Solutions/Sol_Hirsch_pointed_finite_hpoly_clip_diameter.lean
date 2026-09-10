import Solutions.PolynomialHpolyPointedFinal

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

/-- Public-type wrapper for the geometric pointed finite-H-polyhedron clipping
transfer.  Both the internal `ContainsAffineLine` predicate and `finalClip` are
expanded in the theorem type. -/
theorem solution
    {d n : ℕ} {ι : Type*} [Fintype ι]
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty)
    (hpointed : ¬ ∃ x r : EuclideanSpace ℝ (Fin d),
      r ≠ 0 ∧ ∀ t : ℝ, x + t • r ∈ Hpoly a b)
    (f : ι → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (c : ι → ℝ)
    (D : ℕ) (hD : DiamLE (Hpoly a b) D)
    (hPc : IsCompact (Hpoly a b ∩ {y | ∀ i, f i y ≤ c i}))
    (B : ι → ℕ)
    (hB : ∀ i, DiamLE
      ((Hpoly a b ∩ {y | ∀ j, f j y ≤ c j}) ∩ {x | f i x = c i}) (B i)) :
    DiamLE (Hpoly a b ∩ {y | ∀ i, f i y ≤ c i}) (D + 1 + ∑ i, B i) := by
  have hpointed' : ¬ HirschHpolyCap.ContainsAffineLine (Hpoly a b) := by
    simpa [HirschHpolyCap.ContainsAffineLine] using hpointed
  have hPc' : IsCompact (HirschRadial.finalClip (Hpoly a b) f c) := by
    simpa [HirschRadial.finalClip] using hPc
  have hB' : ∀ i, DiamLE
      (HirschRadial.finalClip (Hpoly a b) f c ∩ {x | f i x = c i}) (B i) := by
    intro i
    simpa [HirschRadial.finalClip] using hB i
  have h := HirschHpolyCap.simultaneous_clip_diameter_from_pointed_finite_hpoly
    a b hne hpointed' f c D hD hPc' B hB'
  simpa [HirschRadial.finalClip] using h

#print axioms solution
