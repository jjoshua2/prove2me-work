import Definitions.Def_Hirsch_model

/-!
# Affine-equivalence transport for the Hirsch graph predicates

Reusable infrastructure for slack-normalization arguments.  Mathlib already
provides affine-map preservation of segments/open segments; this file packages
that into the repository's `extremePoints`, `Adj`, and `DiamLE` predicates.
-/

open Set
open scoped RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Hirsch

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- Affine equivalences preserve extreme subsets under image. -/
theorem affineEquiv_isExtreme_image
    (f : E ≃ᵃ[ℝ] F) {A B : Set E} (h : IsExtreme ℝ A B) :
    IsExtreme ℝ (f '' A) (f '' B) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, h.1 hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hzxy
    have hzxy' : z ∈ openSegment ℝ x y := by
      simpa only [← image_openSegment f.toAffineMap x y,
        f.injective.mem_set_image] using hzxy
    exact ⟨x, h.left_mem_of_mem_openSegment hx hy hz hzxy', rfl⟩

/-- Affine equivalences preserve and reflect extreme subsets. -/
theorem affineEquiv_isExtreme_image_iff
    (f : E ≃ᵃ[ℝ] F) {A B : Set E} :
    IsExtreme ℝ (f '' A) (f '' B) ↔ IsExtreme ℝ A B := by
  constructor
  · intro h
    have h' := affineEquiv_isExtreme_image f.symm h
    simpa using h'
  · exact affineEquiv_isExtreme_image f

/-- Affine equivalences carry exactly the extreme points to the extreme points
of the image set. -/
theorem affineEquiv_image_extremePoints
    (f : E ≃ᵃ[ℝ] F) (A : Set E) :
    f '' extremePoints ℝ A = extremePoints ℝ (f '' A) := by
  ext y
  obtain ⟨x, rfl⟩ := f.surjective y
  simp only [f.injective.mem_set_image, mem_extremePoints_iff_left,
    f.injective.eq_iff]
  constructor
  · rintro ⟨hxA, hx⟩
    refine ⟨⟨x, hxA, rfl⟩, ?_⟩
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ hseg
    have hseg' : x ∈ openSegment ℝ u v := by
      simpa only [← image_openSegment f.toAffineMap u v,
        f.injective.mem_set_image] using hseg
    exact congrArg f (hx u hu v hv hseg')
  · rintro ⟨hxA, hx⟩
    refine ⟨hxA, ?_⟩
    intro u hu v hv hseg
    have hseg' : f x ∈ openSegment ℝ (f u) (f v) := by
      simpa only [← image_openSegment f.toAffineMap u v,
        f.injective.mem_set_image] using hseg
    exact f.injective (hx (f u) ⟨u, hu, rfl⟩ (f v) ⟨v, hv, rfl⟩ hseg')

/-- An affine equivalence preserves and reflects graph adjacency. -/
theorem affineEquiv_adj_iff
    (f : E ≃ᵃ[ℝ] F) (A : Set E) (x y : E) :
    Adj (f '' A) (f x) (f y) ↔ Adj A x y := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro hxy
      exact h.1 (congrArg f hxy)
    · have himage : IsExtreme ℝ (f '' A) (f '' segment ℝ x y) := by
        simpa only [image_segment] using h.2
      exact (affineEquiv_isExtreme_image_iff f).mp himage
  · intro h
    refine ⟨?_, ?_⟩
    · intro hxy
      exact h.1 (f.injective hxy)
    · have himage := affineEquiv_isExtreme_image f h.2
      simpa only [image_segment] using himage

/-- A graph-diameter bound transports forward through an affine equivalence. -/
theorem affineEquiv_diamLE_image
    (f : E ≃ᵃ[ℝ] F) (A : Set E) (B : ℕ)
    (h : DiamLE A B) : DiamLE (f '' A) B := by
  intro u hu v hv
  obtain ⟨x, rfl⟩ := f.surjective u
  obtain ⟨y, rfl⟩ := f.surjective v
  have hx : x ∈ extremePoints ℝ A := by
    simpa only [← affineEquiv_image_extremePoints f A,
      f.injective.mem_set_image] using hu
  have hy : y ∈ extremePoints ℝ A := by
    simpa only [← affineEquiv_image_extremePoints f A,
      f.injective.mem_set_image] using hv
  obtain ⟨w, hw0, hwB, hstep⟩ := h x hx y hy
  refine ⟨fun i => f (w i), ?_, ?_, ?_⟩
  · simp only [hw0]
  · simp only [hwB]
  · intro i hi
    rcases hstep i hi with heq | hadj
    · exact Or.inl (congrArg f heq)
    · exact Or.inr ((affineEquiv_adj_iff f A (w i) (w (i + 1))).2 hadj)

/-- `DiamLE` is invariant under affine equivalence. -/
theorem affineEquiv_diamLE_image_iff
    (f : E ≃ᵃ[ℝ] F) (A : Set E) (B : ℕ) :
    DiamLE (f '' A) B ↔ DiamLE A B := by
  constructor
  · intro h
    have h' := affineEquiv_diamLE_image f.symm (f '' A) B h
    simpa using h'
  · exact affineEquiv_diamLE_image f A B

#print axioms affineEquiv_isExtreme_image
#print axioms affineEquiv_image_extremePoints
#print axioms affineEquiv_adj_iff
#print axioms affineEquiv_diamLE_image_iff

end Hirsch
