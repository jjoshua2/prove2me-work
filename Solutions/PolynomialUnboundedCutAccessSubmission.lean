import Mathlib
import Definitions.Def_Hirsch_model
import Solutions.PolynomialUnboundedCutHpoly

open scoped RealInnerProductSpace
open Set Hirsch HirschClip HirschUnboundedCut

set_option maxHeartbeats 4000000

noncomputable section

/-- The specified cutting face is reachable in B+1 steps from every clipped
vertex. Only the clip is assumed bounded, not the outer H-polyhedron.
The conclusion is not a walk to the particular supplied target vertex. -/
theorem solution
    (d n B : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (β : ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β}))
    (hQ : DiamLE (Hpoly a b) B)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β}))
    (hv : v ∈ extremePoints ℝ (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β}))
    (hvc : ⟪c, v⟫ = β) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β}) ∧
      ⟪c, z⟫ = β ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (B + 1) = z ∧
        ∀ j < B + 1,
          w j = w (j + 1) ∨
            Adj (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β}) (w j) (w (j + 1)) := by
  obtain ⟨D, hw⟩ := bounded_hpoly_clip_connected a b c β hbd u hu v hv
  exact cut_access_of_outer_diameter_and_path (Hpoly a b) (hpoly_convex a b)
    c β B hQ hu hvc hw

#print axioms solution
