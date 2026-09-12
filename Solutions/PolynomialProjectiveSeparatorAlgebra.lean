import Mathlib

/-!
# Algebra behind automatic projective factor discovery

A homogeneous describing row is (a,-b). Its image under shearProjection c is
exactly a-b*c. The common kernel line is the candidate hyperplane at infinity.
These primitives are independent of the geometry in #203. The dimension/rank
recognition proof and its precise scope are recorded in the companion note.
Verification receipts are maintained separately from the mathematical source.
-/
set_option autoImplicit false
noncomputable section

namespace HirschProjectiveDiscovery

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- Quotient the homogeneous row space by the proposed infinity line. -/
def shearProjection (c : E) : (E × ℝ) →ₗ[ℝ] E where
  toFun z := z.1 + z.2 • c
  map_add' x y := by
    change x.1 + y.1 + (x.2 + y.2) • c =
      (x.1 + x.2 • c) + (y.1 + y.2 • c)
    rw [add_smul]
    abel
  map_smul' t x := by
    change t • x.1 + (t * x.2) • c = t • (x.1 + x.2 • c)
    rw [smul_add, smul_smul]

@[simp] theorem shearProjection_row (c a : E) (b : ℝ) :
    shearProjection c (a, -b) = a - b • c := by
  simp [shearProjection, sub_eq_add_neg]

@[simp] theorem shearProjection_horizon (c : E) :
    shearProjection c (c, (-1 : ℝ)) = 0 := by
  simp [shearProjection]

/-- Every kernel element lies on the single line through (c,-1). -/
theorem shearProjection_kernel_vector (c : E) (z : E × ℝ)
    (hz : shearProjection c z = 0) :
    z = (-z.2) • (c, (-1 : ℝ)) := by
  apply Prod.ext
  · change z.1 = (-z.2) • c
    have h : z.1 + z.2 • c = 0 := hz
    have he : z.1 = -(z.2 • c) := eq_neg_of_add_eq_zero_left h
    simpa using he
  · simp

/-- The normalized chart is unique once its kernel line is known. -/
theorem shearProjection_chart_unique (c q : E)
    (h : (shearProjection c).ker ≤ (shearProjection q).ker) : c = q := by
  have hc : (c, (-1 : ℝ)) ∈ (shearProjection c).ker := by
    apply LinearMap.mem_ker.mpr
    exact shearProjection_horizon c
  have he := LinearMap.mem_ker.mp (h hc)
  change c + (-1 : ℝ) • q = 0 at he
  have hsub : c - q = 0 := by simpa [sub_eq_add_neg] using he
  exact sub_eq_zero.mp hsub

/-- If the two homogeneous block spans meet only in the kernel and the kernel
is contained in the second span, their projected spans have no nonzero overlap.
This proves directness after quotienting; it is not a graph assumption. -/
theorem common_projected_vector_eq_zero
    (f : E →ₗ[ℝ] F) (U V : Submodule ℝ E)
    (hker : f.ker ≤ V) (hinter : U ⊓ V ≤ f.ker)
    {x y : E} (hx : x ∈ U) (hy : y ∈ V) (hxy : f x = f y) :
    f x = 0 := by
  have hdiff : x - y ∈ f.ker := by
    apply LinearMap.mem_ker.mpr
    rw [map_sub, hxy, sub_self]
  have hxV : x ∈ V := by
    have h := V.add_mem (hker hdiff) hy
    simpa using h
  exact LinearMap.mem_ker.mp (hinter ⟨hx, hxV⟩)

/-- If the homogeneous spans cover the row space, the projected spans cover
the target space whenever the projection is surjective. -/
theorem projected_spans_cover
    (f : E →ₗ[ℝ] F) (hf : Function.Surjective f)
    (U V : Submodule ℝ E) (hUV : U ⊔ V = ⊤) :
    U.map f ⊔ V.map f = ⊤ := by
  rw [← Submodule.map_sup, hUV, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr hf

#print axioms shearProjection_kernel_vector
#print axioms shearProjection_chart_unique
#print axioms common_projected_vector_eq_zero
#print axioms projected_spans_cover
end HirschProjectiveDiscovery
