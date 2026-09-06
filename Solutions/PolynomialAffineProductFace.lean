import Mathlib
import Solutions.PolynomialProductWalk

open Set Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschProduct

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- Pull an ambient extreme point back through an injective affine face chart. -/
lemma extreme_preimage (f : E →ᵃ[ℝ] F) (hinj : Function.Injective f)
    (Q : Set E) (P : Set F) (hsub : f '' Q ⊆ P)
    {q : E} (hq : q ∈ Q) (hext : f q ∈ extremePoints ℝ P) :
    q ∈ extremePoints ℝ Q := by
  refine ⟨hq, ?_⟩
  intro p hp r hr hop
  have hmap : f q ∈ openSegment ℝ (f p) (f r) := by
    rw [← image_openSegment ℝ f p r]
    exact ⟨q, hop, rfl⟩
  exact hinj (hext.2 (hsub ⟨p, hp, rfl⟩) (hsub ⟨r, hr, rfl⟩) hmap)

/-- Injective affine maps preserve edges of a set onto its affine image. -/
lemma adj_affine_image (f : E →ᵃ[ℝ] F) (hinj : Function.Injective f)
    (Q : Set E) {p q : E} (hadj : Adj Q p q) :
    Adj (f '' Q) (f p) (f q) := by
  refine ⟨fun h => hadj.1 (hinj h), ?_, ?_⟩
  · intro z hz
    rw [← image_segment ℝ f p q] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact ⟨t, hadj.2.subset ht, rfl⟩
  · intro x hx y hy z hz hop
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    rw [← image_segment ℝ f p q] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    rw [← image_openSegment ℝ f x' y'] at hop
    obtain ⟨t, ht, htz⟩ := hop
    have heq : t = z' := hinj htz
    subst t
    rw [← image_segment ℝ f p q]
    exact ⟨x', hadj.2.left_mem_of_mem_openSegment hx' hy' hz' ht, rfl⟩

/-- A walk in an affine product face gives a parent-polytope walk with exactly
the same budget. The chart need not be orthogonal; shears are allowed. -/
lemma walk_via_affine_face
    (P : Set F) (Q : Set E) (f : E →ᵃ[ℝ] F)
    (hinj : Function.Injective f) (hface : IsExtreme ℝ P (f '' Q))
    (u x : F) (hu : u ∈ extremePoints ℝ P) (hx : x ∈ extremePoints ℝ P)
    (hui : u ∈ f '' Q) (hxi : x ∈ f '' Q)
    (B : ℕ) (hD : DiamLE Q B) :
    ∃ w : ℕ → F, w 0 = u ∧ w B = x ∧
      ∀ j < B, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)) := by
  obtain ⟨qu, hqu, hfu⟩ := hui
  obtain ⟨qx, hqx, hfx⟩ := hxi
  have heu : qu ∈ extremePoints ℝ Q :=
    extreme_preimage f hinj Q P hface.subset hqu (by simpa only [hfu] using hu)
  have hex : qx ∈ extremePoints ℝ Q :=
    extreme_preimage f hinj Q P hface.subset hqx (by simpa only [hfx] using hx)
  obtain ⟨wq, hw0, hwB, hws⟩ := hD qu heu qx hex
  refine ⟨fun j => f (wq j), ?_, ?_, ?_⟩
  · rw [hw0, hfu]
  · rw [hwB, hfx]
  · intro j hj
    rcases hws j hj with h | h
    · exact Or.inl (congrArg f h)
    · have hi := adj_affine_image f hinj Q h
      exact Or.inr ⟨hi.1, hface.trans hi.2⟩

#print axioms walk_via_affine_face

end HirschProduct
