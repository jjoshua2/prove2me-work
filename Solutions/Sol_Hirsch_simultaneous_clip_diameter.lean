import Solutions.PolynomialClippingDiameter

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

/-- Offline public-facing wrapper. No private helper vocabulary occurs in the
type, and this file performs no Prove2Me registration or submission. -/
theorem solution {d n : ℕ}
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQ : Convex ℝ Q) (hQc : IsCompact Q)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (o : EuclideanSpace ℝ (Fin d)) (ho : o ∈ Q) (hs : ∀ i, ⟪a i, o⟫ < b i)
    (D : ℕ) (hD : DiamLE Q D)
    (B : Fin n → ℕ)
    (hB : ∀ i, DiamLE ((Q ∩ Hpoly a b) ∩ {x | ⟪a i, x⟫ = b i}) (B i)) :
    DiamLE (Q ∩ Hpoly a b) (D + ∑ i, B i) := by
  exact HirschRadial.simultaneous_clip_diameter Q hQ hQc
    (fun i => innerSL ℝ (a i)) b o ho hs D hD B hB

#print axioms solution
