import Solutions.PolynomialHpolyAutoCapLevel

/-! End-to-end finite H-polyhedron clipping theorem with the far cap chosen
internally from compactness of the final clipped set. -/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRadial

noncomputable section
namespace HirschHpolyCap

variable {d n : ℕ} {ι : Type*} [Fintype ι]

/-- For a finite H-polyhedron whose row normals have no nonzero common-kernel
direction, a compact simultaneous clip inherits the old graph-diameter bound
with one unboundedness correction plus the intrinsic budgets of the final cut
faces.  The canonical far-cap level is chosen internally. -/
theorem simultaneous_clip_diameter_from_finite_hpoly
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (f : ι → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (c : ι → ℝ)
    (hkernel : ∀ r : EuclideanSpace ℝ (Fin d),
      (∀ j, ⟪a j, r⟫ = 0) → r = 0)
    (D : ℕ) (hD : DiamLE (Hpoly a b) D)
    (hPc : IsCompact (finalClip (Hpoly a b) f c))
    (B : ι → ℕ)
    (hB : ∀ i, DiamLE (finalClip (Hpoly a b) f c ∩ {x | f i x = c i}) (B i)) :
    DiamLE (finalClip (Hpoly a b) f c) (D + 1 + ∑ i, B i) := by
  obtain ⟨T, hOldBelow, hFinalBelow⟩ :=
    exists_far_cap_level a b (finalClip (Hpoly a b) f c) hPc
  exact simultaneous_clip_diameter_from_finite_hpoly_far_cap
    a b f c T hkernel D hD hOldBelow hFinalBelow B hB

#print axioms simultaneous_clip_diameter_from_finite_hpoly

end HirschHpolyCap
