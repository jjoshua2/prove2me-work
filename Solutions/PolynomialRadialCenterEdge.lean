import Mathlib
import Solutions.PolynomialRadialRetraction

open scoped RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
namespace HirschRadial

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- Radial retraction cannot leave a segment whose first endpoint is the
retraction centre.  This is purely convex geometry and does not require the
ambient outer set. -/
theorem retract_mem_center_segment
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (o y z : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ segment ℝ o y) :
    retract a b o z ∈ segment ℝ o y := by
  change point o z (scale (fun i => normalizedRow (a i) (b i) o z)) ∈
    segment ℝ o y
  exact point_mem_convex (segment ℝ o y) (convex_segment o y)
    (left_mem_segment ℝ o y) hz (one_le_scale _)

/-- If the centre and outer endpoint lie in one convex outer region, every
point on their segment retracts into the clipped part of that SAME segment.
Thus a centre-to-old-vertex edge needs only its old-edge subsegment repair
region; final cut-face labels are unnecessary for this piece of the trace. -/
theorem retract_center_segment_mem_clip_subsegment
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (o y z : EuclideanSpace ℝ (Fin d))
    (ho : o ∈ Q) (hy : y ∈ Q)
    (hstrict : ∀ i, ⟪a i, o⟫ < b i)
    (hz : z ∈ segment ℝ o y) :
    retract a b o z ∈ clipSet Q a b ∩ segment ℝ o y := by
  have hzQ : z ∈ Q := hQ.segment_subset ho hy hz
  exact ⟨retract_mem Q hQ a b o z ho hzQ hstrict,
    retract_mem_center_segment a b o y z hz⟩

/-- Set-level form used by target-cone/star routing: the full radial image of a
centre edge is contained in one clipped old-edge subsegment. -/
theorem retract_image_center_segment_subset_clip_subsegment
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (o y : EuclideanSpace ℝ (Fin d))
    (ho : o ∈ Q) (hy : y ∈ Q)
    (hstrict : ∀ i, ⟪a i, o⟫ < b i) :
    retract a b o '' segment ℝ o y ⊆
      clipSet Q a b ∩ segment ℝ o y := by
  rintro z ⟨x, hx, rfl⟩
  exact retract_center_segment_mem_clip_subsegment
    Q hQ a b o y x ho hy hstrict hx

#print axioms retract_mem_center_segment
#print axioms retract_center_segment_mem_clip_subsegment
#print axioms retract_image_center_segment_subset_clip_subsegment

end HirschRadial
