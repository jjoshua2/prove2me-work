import Solutions.PolynomialHpolyPointedness

/-! Geometric pointed finite-H-polyhedron version of the simultaneous clipping
transfer. -/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRadial

noncomputable section
namespace HirschHpolyCap

variable {d n : ℕ} {ι : Type*} [Fintype ι]

/-- Let `Q = Hpoly a b` be nonempty and pointed in the geometric sense that it
contains no affine line.  If the old vertex-edge graph has padded diameter at
most `D`, the simultaneous clip is compact, and final cut face `i` has intrinsic
graph diameter at most `B i`, then the final clipped polytope has padded graph
diameter at most `D + 1 + Σ_i B i`. -/
theorem simultaneous_clip_diameter_from_pointed_finite_hpoly
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty)
    (hpointed : ¬ ContainsAffineLine (Hpoly a b))
    (f : ι → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (c : ι → ℝ)
    (D : ℕ) (hD : DiamLE (Hpoly a b) D)
    (hPc : IsCompact (finalClip (Hpoly a b) f c))
    (B : ι → ℕ)
    (hB : ∀ i, DiamLE (finalClip (Hpoly a b) f c ∩ {x | f i x = c i}) (B i)) :
    DiamLE (finalClip (Hpoly a b) f c) (D + 1 + ∑ i, B i) := by
  have hkernel : ∀ r : EuclideanSpace ℝ (Fin d),
      (∀ j, ⟪a j, r⟫ = 0) → r = 0 :=
    (no_affine_line_iff_no_common_kernel a b hne).1 hpointed
  exact simultaneous_clip_diameter_from_finite_hpoly
    a b f c hkernel D hD hPc B hB

#print axioms simultaneous_clip_diameter_from_pointed_finite_hpoly

end HirschHpolyCap
