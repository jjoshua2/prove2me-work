import Definitions.Def_Hirsch_model

/-!
# Segment-chart transport of the ordinary vertex-edge graph

A chart need only be injective on a convex domain; it need not be affine or
injective on the entire ambient vector space. This is the transport primitive
for a positive-denominator projective chart. Mathematical proof candidate;
new declarations have not yet been compiled in the pinned Lean environment.
-/
open Set
set_option autoImplicit false
noncomputable section

namespace Hirsch

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- A segment-preserving embedding of a convex domain. Both image identities
are required: an arbitrary nonlinear injection is insufficient for edge transport. -/
structure SegmentChart (U : Set E) (f : E → F) : Prop where
  convex : Convex ℝ U
  injOn : Set.InjOn f U
  segment_image : ∀ x ∈ U, ∀ y ∈ U,
    f '' segment ℝ x y = segment ℝ (f x) (f y)
  openSegment_image : ∀ x ∈ U, ∀ y ∈ U,
    f '' openSegment ℝ x y = openSegment ℝ (f x) (f y)

namespace SegmentChart

variable {U : Set E} {f : E → F} (h : SegmentChart U f)

/-- Preserve and reflect extreme subsets without assuming a global inverse. -/
theorem isExtreme_image_iff {P C : Set E}
    (hP : P ⊆ U) (hC : C ⊆ U) :
    IsExtreme ℝ (f '' P) (f '' C) ↔ IsExtreme ℝ P C := by
  constructor
  · intro he
    refine ⟨?_, ?_⟩
    · intro z hz
      obtain ⟨x, hx, hxf⟩ := he.1 ⟨z, hz, rfl⟩
      have hxz := h.injOn (hP hx) (hC hz) hxf
      simpa [hxz] using hx
    · intro x hx y hy z hz hseg
      have hfseg : f z ∈ openSegment ℝ (f x) (f y) := by
        rw [← h.openSegment_image x (hP hx) y (hP hy)]
        exact ⟨z, hseg, rfl⟩
      obtain ⟨t, ht, htf⟩ := he.left_mem_of_mem_openSegment
        ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩ hfseg
      have htx := h.injOn (hC ht) (hP hx) htf
      simpa [htx] using ht
  · intro he
    refine ⟨?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨z, he.1 hz, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hseg
      rw [← h.openSegment_image x (hP hx) y (hP hy)] at hseg
      obtain ⟨t, ht, htf⟩ := hseg
      have htU : t ∈ U := h.convex.segment_subset (hP hx) (hP hy)
        (openSegment_subset_segment ht)
      have htz := h.injOn htU (hC hz) htf
      subst t
      exact ⟨x, he.left_mem_of_mem_openSegment hx hy hz ht, rfl⟩

/-- A segment chart carries exactly the parent vertices to image vertices. -/
theorem image_extremePoints (P : Set E) (hP : P ⊆ U) :
    f '' extremePoints ℝ P = extremePoints ℝ (f '' P) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hxU : ({x} : Set E) ⊆ U := by
      intro z hz
      simpa only [Set.mem_singleton_iff.mp hz] using hP hx.1
    have he := (h.isExtreme_image_iff hP hxU).2 (isExtreme_singleton.mpr hx)
    exact isExtreme_singleton.mp (by simpa using he)
  · intro y hy
    obtain ⟨x, hxP, rfl⟩ := hy.1
    have hxU : ({x} : Set E) ⊆ U := by
      intro z hz
      simpa only [Set.mem_singleton_iff.mp hz] using hP hxP
    have he : IsExtreme ℝ (f '' P) (f '' ({x} : Set E)) := by
      simpa using isExtreme_singleton.mpr hy
    exact ⟨x, isExtreme_singleton.mp ((h.isExtreme_image_iff hP hxU).1 he), rfl⟩

/-- Ordinary adjacency, not circuit adjacency, is invariant on the chart. -/
theorem adj_iff (P : Set E) (hP : P ⊆ U)
    (x y : E) (hx : x ∈ U) (hy : y ∈ U) :
    Adj (f '' P) (f x) (f y) ↔ Adj P x y := by
  have hS : segment ℝ x y ⊆ U := h.convex.segment_subset hx hy
  have hface := h.isExtreme_image_iff hP hS
  rw [h.segment_image x hx y hy] at hface
  constructor
  · rintro ⟨hne, he⟩
    exact ⟨fun hxy => hne (congrArg f hxy), hface.mp he⟩
  · rintro ⟨hne, he⟩
    exact ⟨fun hfxy => hne (h.injOn hx hy hfxy), hface.mpr he⟩

/-- The same padded number of ordinary edges works in the image. -/
theorem diamLE_image (P : Set E) (hP : P ⊆ U) (B : ℕ)
    (hdiam : DiamLE P B) : DiamLE (f '' P) B := by
  intro u hu v hv
  rw [← h.image_extremePoints P hP] at hu hv
  obtain ⟨x, hx, rfl⟩ := hu
  obtain ⟨y, hy, rfl⟩ := hv
  obtain ⟨w, hw0, hwB, hs⟩ := hdiam x hx y hy
  refine ⟨fun i => f (w i), by simp [hw0], by simp [hwB], ?_⟩
  intro i hi
  rcases hs i hi with heq | hadj
  · exact Or.inl (congrArg f heq)
  · have hxP : w i ∈ P := hadj.2.1 (left_mem_segment ℝ _ _)
    have hyP : w (i + 1) ∈ P := hadj.2.1 (right_mem_segment ℝ _ _)
    exact Or.inr ((h.adj_iff P hP _ _ (hP hxP) (hP hyP)).2 hadj)

end SegmentChart

#print axioms SegmentChart.isExtreme_image_iff
#print axioms SegmentChart.image_extremePoints
#print axioms SegmentChart.adj_iff
#print axioms SegmentChart.diamLE_image
end Hirsch
