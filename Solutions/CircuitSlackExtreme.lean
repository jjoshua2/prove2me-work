import Solutions.CircuitSlackTranslation

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped RealInnerProductSpace
open Hirsch Set Affine

namespace HirschCircuit

/-- The slack parametrization as an affine map. -/
noncomputable def slackAffineMap {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] (Fin n → ℝ) where
  toFun := slack a b
  linear := -(rowMap a)
  map_vadd' p v := by
    funext i
    simp only [slack, rowMap, inner_add_right, LinearMap.neg_apply,
      LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply]
    ring

@[simp] theorem slackAffineMap_apply {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    slackAffineMap a b x = slack a b x := rfl

theorem slackAffineMap_injective_of_rowMap_injective {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (rowMap a)) :
    Function.Injective (slackAffineMap a b) := by
  simpa [slackAffineMap] using slack_injective_of_rowMap_injective a b hinj

theorem image_slackAffineMap_Hpoly {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    slackAffineMap a b '' Hpoly a b = SlackPoly a b := by
  ext s
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, (slack_nonneg_iff_mem_Hpoly a b x).mpr hx⟩
  · rintro ⟨⟨x, rfl⟩, hs⟩
    exact ⟨x, (slack_nonneg_iff_mem_Hpoly a b x).mp hs, rfl⟩

/-- An injective affine map sends extreme points to extreme points of its image. -/
theorem mem_extremePoints_image_of_affine_injective
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (f : E →ᵃ[ℝ] F) (hinj : Function.Injective f)
    (S : Set E) (x : E)
    (hx : x ∈ extremePoints ℝ S) :
    f x ∈ extremePoints ℝ (f '' S) := by
  rw [mem_extremePoints] at hx ⊢
  refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
  rintro _ ⟨x₁, hx₁, rfl⟩ _ ⟨x₂, hx₂, rfl⟩ hseg
  have hxseg : x ∈ openSegment ℝ x₁ x₂ := by
    have hseg' : f x ∈ f '' openSegment ℝ x₁ x₂ := by
      rw [image_openSegment]
      exact hseg
    rcases hseg' with ⟨z, hz, hzx⟩
    have hzx' : z = x := hinj hzx
    simpa [hzx'] using hz
  rcases hx.2 x₁ hx₁ x₂ hx₂ hxseg with ⟨h₁, h₂⟩
  exact ⟨congrArg f h₁, congrArg f h₂⟩

/-- Vertices of the original H-polytope become vertices of its slack image. -/
theorem slack_mem_extremePoints_of_mem_extremePoints {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (rowMap a))
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b)) :
    slack a b x ∈ extremePoints ℝ (SlackPoly a b) := by
  have h := mem_extremePoints_image_of_affine_injective
    (slackAffineMap a b)
    (slackAffineMap_injective_of_rowMap_injective a b hinj)
    (Hpoly a b) x hx
  rw [image_slackAffineMap_Hpoly a b] at h
  exact h

#print axioms image_slackAffineMap_Hpoly
#print axioms mem_extremePoints_image_of_affine_injective
#print axioms slack_mem_extremePoints_of_mem_extremePoints

end HirschCircuit
