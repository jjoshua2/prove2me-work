import Definitions.Def_Hirsch_model

/-!
# Affine-equivalence transport for the Hirsch graph predicates

Reusable infrastructure for slack-normalization arguments. Mathlib already
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

private theorem affineEquiv_image_segment
    (f : E ≃ᵃ[ℝ] F) (x y : E) :
    f '' segment ℝ x y = segment ℝ (f x) (f y) := by
  simpa only [AffineEquiv.coe_toAffineMap] using
    (image_segment ℝ f.toAffineMap x y)

private theorem affineEquiv_image_openSegment
    (f : E ≃ᵃ[ℝ] F) (x y : E) :
    f '' openSegment ℝ x y = openSegment ℝ (f x) (f y) := by
  simpa only [AffineEquiv.coe_toAffineMap] using
    (image_openSegment ℝ f.toAffineMap x y)

/-- Affine equivalences preserve extreme subsets under image. -/
theorem affineEquiv_isExtreme_image
    (f : E ≃ᵃ[ℝ] F) {A B : Set E} (h : IsExtreme ℝ A B) :
    IsExtreme ℝ (f '' A) (f '' B) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, h.1 hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hzxy
    have hzimg : f z ∈ f '' openSegment ℝ x y := by
      rw [affineEquiv_image_openSegment f x y]
      exact hzxy
    rcases hzimg with ⟨z', hz', hz'eq⟩
    have hzz' : z' = z := f.injective hz'eq
    subst z'
    exact ⟨x, h.left_mem_of_mem_openSegment hx hy hz hz', rfl⟩

/-- Affine equivalences preserve and reflect extreme subsets. -/
theorem affineEquiv_isExtreme_image_iff
    (f : E ≃ᵃ[ℝ] F) {A B : Set E} :
    IsExtreme ℝ (f '' A) (f '' B) ↔ IsExtreme ℝ A B := by
  constructor
  · intro h
    have h' := affineEquiv_isExtreme_image f.symm h
    have hbackA : f.symm '' (f '' A) = A := by
      ext x
      simp
    have hbackB : f.symm '' (f '' B) = B := by
      ext x
      simp
    rw [hbackA, hbackB] at h'
    exact h'
  · exact affineEquiv_isExtreme_image f

/-- Affine equivalences carry exactly the extreme points to the extreme points
of the image set. -/
theorem affineEquiv_image_extremePoints
    (f : E ≃ᵃ[ℝ] F) (A : Set E) :
    f '' extremePoints ℝ A = extremePoints ℝ (f '' A) := by
  ext b
  obtain ⟨a, rfl⟩ := f.surjective b
  have himage : ∀ x y, f '' openSegment ℝ x y = openSegment ℝ (f x) (f y) :=
    affineEquiv_image_openSegment f
  simp only [mem_extremePoints, f.surjective.forall,
    f.injective.mem_set_image, f.injective.eq_iff, ← himage]

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
        rw [affineEquiv_image_segment f x y]
        exact h.2
      exact (affineEquiv_isExtreme_image_iff f).mp himage
  · intro h
    refine ⟨?_, ?_⟩
    · intro hxy
      exact h.1 (f.injective hxy)
    · have himage := affineEquiv_isExtreme_image f h.2
      rw [affineEquiv_image_segment f x y] at himage
      exact himage

/-- A graph-diameter bound transports forward through an affine equivalence. -/
theorem affineEquiv_diamLE_image
    (f : E ≃ᵃ[ℝ] F) (A : Set E) (B : ℕ)
    (h : DiamLE A B) : DiamLE (f '' A) B := by
  intro u hu v hv
  obtain ⟨x, rfl⟩ := f.surjective u
  obtain ⟨y, rfl⟩ := f.surjective v
  have hximg : f x ∈ f '' extremePoints ℝ A := by
    rw [affineEquiv_image_extremePoints f A]
    exact hu
  have hyimg : f y ∈ f '' extremePoints ℝ A := by
    rw [affineEquiv_image_extremePoints f A]
    exact hv
  have hx : x ∈ extremePoints ℝ A := f.injective.mem_set_image.mp hximg
  have hy : y ∈ extremePoints ℝ A := f.injective.mem_set_image.mp hyimg
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
    have hback : f.symm '' (f '' A) = A := by
      ext x
      simp
    rw [hback] at h'
    exact h'
  · exact affineEquiv_diamLE_image f A B

#print axioms affineEquiv_isExtreme_image
#print axioms affineEquiv_image_extremePoints
#print axioms affineEquiv_adj_iff
#print axioms affineEquiv_diamLE_image_iff

end Hirsch
