import Mathlib
import Definitions.Def_Hirsch_model
import Solutions.PolynomialClipSplice

open scoped RealInnerProductSpace
open Set Hirsch HirschCut HirschClip

set_option maxHeartbeats 4000000

noncomputable section

/-- Full diameter after one halfspace cut, with an explicit outer vertex on
or beyond the plane. This form does not require compactness. -/
theorem HirschClip.clipped_diameter_of_outer_vertex
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

/-- Compactness supplies an extreme maximizer on or beyond a plane as soon
as any point of the set lies on or beyond it. -/
lemma HirschClip.compact_extreme_ge
    {d : ℕ} (Q : Set (EuclideanSpace ℝ (Fin d))) (hcompact : IsCompact Q)
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Q) (hxc : b ≤ ⟪c, x⟫) :
    ∃ v ∈ extremePoints ℝ Q, b ≤ ⟪c, v⟫ := by
  have hf : Continuous (fun y : EuclideanSpace ℝ (Fin d) => ⟪c, y⟫) :=
    continuous_const.inner continuous_id
  obtain ⟨p, hpQ, hpmax⟩ := hcompact.exists_isMaxOn ⟨x, hx⟩ hf.continuousOn
  let F := Q ∩ {y | ⟪c, y⟫ = ⟪c, p⟫}
  have hFcompact : IsCompact F := hcompact.inter_right (isClosed_eq hf continuous_const)
  have hFnonempty : F.Nonempty := ⟨p, hpQ, rfl⟩
  obtain ⟨v, hvF⟩ := hFcompact.extremePoints_nonempty hFnonempty
  have hretain : Q ∩ {y | ⟪c, y⟫ ≤ ⟪c, p⟫} = Q := by
    ext y
    constructor
    · exact fun hy => hy.1
    · intro hy
      exact ⟨hy, hpmax hy⟩
  have hface : IsExtreme ℝ Q F := by
    simpa only [hretain] using cut_face_isExtreme Q c ⟪c, p⟫
  refine ⟨v, hface.extremePoints_subset_extremePoints hvF, ?_⟩
  have hvmax : ⟪c, v⟫ = ⟪c, p⟫ := hvF.1.2
  calc
    b ≤ ⟪c, x⟫ := hxc
    _ ≤ ⟪c, p⟫ := hpmax hx
    _ = ⟪c, v⟫ := hvmax.symm

/-- The full clipped diameter is bounded by outer diameter plus cut-face
diameter. No crossing witness is required for compact convex Q. The bound
covers every pair of clipped vertices, including vertices created by the cut.
This is a transfer of two assumed bounds, not a uniform polynomial bound. -/
theorem solution
    (d B C : ℕ) (Q : Set (EuclideanSpace ℝ (Fin d)))
    (hcompact : IsCompact Q) (hconv : Convex ℝ Q)
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    (hQ : DiamLE Q B)
    (hF : DiamLE (Q ∩ {x | ⟪c, x⟫ = b}) C) :
    DiamLE (Q ∩ {x | ⟪c, x⟫ ≤ b}) (B + C) := by
  classical
  by_cases hex : ∃ x ∈ Q, b ≤ ⟪c, x⟫
  · obtain ⟨x, hx, hxc⟩ := hex
    obtain ⟨v, hv, hvc⟩ := compact_extreme_ge Q hcompact c b hx hxc
    exact clipped_diameter_of_outer_vertex d B C Q hconv c b v hv hvc hQ hF
  · have hretain : Q ∩ {x | ⟪c, x⟫ ≤ b} = Q := by
      ext x
      constructor
      · exact fun hx => hx.1
      · intro hx
        have hlt : ⟪c, x⟫ < b := lt_of_not_ge (fun h => hex ⟨x, hx, h⟩)
        exact ⟨hx, hlt.le⟩
    rw [hretain]
    intro u hu v hv
    exact walk_pad (Nat.le_add_right B C) (hQ u hu v hv)

#print axioms HirschClip.clipped_diameter_of_outer_vertex
#print axioms solution
