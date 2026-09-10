import Mathlib
import Definitions.Def_Hirsch_model
import Solutions.PolynomialUnboundedCutHpoly

open scoped RealInnerProductSpace
open Set Hirsch HirschClip HirschUnboundedCut

set_option maxHeartbeats 4000000

noncomputable section

/-- A bounded clip of a possibly unbounded H-polyhedron has diameter at most
outer vertex-graph diameter plus cut-face diameter plus one. Empty clips and
zero normals are allowed. The two assumed numerical bounds are not derived
from row count, so this is not an unrestricted polynomial Hirsch theorem. -/
theorem solution
    (d n B C : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (β : ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β}))
    (hQ : DiamLE (Hpoly a b) B)
    (hF : DiamLE (Hpoly a b ∩ {x | ⟪c, x⟫ = β}) C) :
    DiamLE (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β}) (B + C + 1) := by
  apply clipped_diameter_of_outer_and_connected_clip
    (Hpoly a b) (hpoly_convex a b) c β B C hQ hF
  intro u hu v hv
  exact bounded_hpoly_clip_connected a b c β hbd u hu v hv

#print axioms solution
