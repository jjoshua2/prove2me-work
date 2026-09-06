import Mathlib
import Definitions.Def_Hirsch_model
import Solutions.PolynomialClipSplice

open scoped RealInnerProductSpace
open Set Hirsch HirschCut HirschClip

set_option maxHeartbeats 4000000

noncomputable section

/-- Full diameter after one halfspace cut. The two retained portions of a
single outer walk share B steps; crossing the new face costs at most C.
An outer vertex on or beyond the plane is necessary in this generality:
without it, an unbounded ray with vertex diameter zero is a counterexample.
This transfers two assumed bounds, not a uniform polynomial Hirsch bound. -/
theorem solution
    (d B C : ℕ) (Q : Set (EuclideanSpace ℝ (Fin d)))
    (hconv : Convex ℝ Q)
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ Q) (hvc : b ≤ ⟪c, v⟫)
    (hQ : DiamLE Q B)
    (hF : DiamLE (Q ∩ {x | ⟪c, x⟫ = b}) C) :
    DiamLE (Q ∩ {x | ⟪c, x⟫ ≤ b}) (B + C) := by
  intro u hu w hw
  by_cases huc : ⟪c, u⟫ = b
  · by_cases hwc : ⟪c, w⟫ = b
    · exact walk_pad (by omega : C ≤ B + C) (cut_face_walk Q c b C hF hu hw huc hwc)
    · have hwlt : ⟪c, w⟫ < b := lt_of_le_of_ne hw.1.2 hwc
      have hwQ := strict_cut_extreme_to_parent Q hconv c b hw hwlt
      obtain ⟨z, hz, hcz, hwz⟩ := outer_cut_walk Q c b B hQ hwQ hv hwlt hvc
      have hzu := cut_face_walk Q c b C hF hz hu hcz huc
      exact walk_reverse (walk_append hwz hzu)
  · have hult : ⟪c, u⟫ < b := lt_of_le_of_ne hu.1.2 huc
    have huQ := strict_cut_extreme_to_parent Q hconv c b hu hult
    by_cases hwc : ⟪c, w⟫ = b
    · obtain ⟨z, hz, hcz, huz⟩ := outer_cut_walk Q c b B hQ huQ hv hult hvc
      exact walk_append huz (cut_face_walk Q c b C hF hz hw hcz hwc)
    · have hwlt : ⟪c, w⟫ < b := lt_of_le_of_ne hw.1.2 hwc
      have hwQ := strict_cut_extreme_to_parent Q hconv c b hw hwlt
      obtain ⟨p, hp0, hpB, hps⟩ := hQ u huQ w hwQ
      have h0 : ⟪c, p 0⟫ < b := by simpa only [hp0] using hult
      have hB : ⟪c, p B⟫ < b := by simpa only [hpB] using hwlt
      have hspliced := splice_outer_walk d B C Q c b hF p h0 hB hps
      simpa only [hp0, hpB] using hspliced

#print axioms solution
