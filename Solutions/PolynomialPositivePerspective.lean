import Solutions.PolynomialSegmentChartTransport

/-!
# Positive projective charts preserve the ordinary edge graph

The map x |-> x / (1 + l(x)) has inverse y |-> y / (1 - l(y)) on the
respective positive-denominator domains. Explicit segment reweighting, not an
assumed projective-invariance axiom, supplies the transport certificate.
The kernel and axiom verification receipts are maintained separately.
-/
open Set
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace HirschPerspective

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def denominator (l : E →ₗ[ℝ] ℝ) (x : E) : ℝ := 1 + l x

def perspective (l : E →ₗ[ℝ] ℝ) (x : E) : E :=
  (denominator l x)⁻¹ • x

def positiveDomain (l : E →ₗ[ℝ] ℝ) : Set E :=
  {x | 0 < denominator l x}

lemma denominator_mix (l : E →ₗ[ℝ] ℝ) (x y : E) (a b : ℝ)
    (hab : a + b = 1) :
    denominator l (a • x + b • y) = a * denominator l x + b * denominator l y := by
  simp only [denominator, map_add, map_smul, smul_eq_mul]
  nlinarith

private lemma weighted_pos {a b s t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hs : 0 < s) (ht : 0 < t) : 0 < a*s + b*t := by
  rcases eq_or_lt_of_le ha with hzero | hpos
  · have ha0 : a = 0 := hzero.symm
    have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using ht
  · exact add_pos_of_pos_of_nonneg (mul_pos hpos hs) (mul_nonneg hb ht.le)

lemma positiveDomain_convex (l : E →ₗ[ℝ] ℝ) : Convex ℝ (positiveDomain l) := by
  intro x hx y hy a b ha hb hab
  change 0 < denominator l (a • x + b • y)
  rw [denominator_mix l x y a b hab]
  exact weighted_pos ha hb hab hx hy

lemma denominator_neg_perspective (l : E →ₗ[ℝ] ℝ) (x : E)
    (hx : denominator l x ≠ 0) :
    denominator (-l) (perspective l x) = (denominator l x)⁻¹ := by
  have hx' : 1 + l x ≠ 0 := hx
  simp only [denominator, perspective, LinearMap.neg_apply, map_smul, smul_eq_mul]
  field_simp [hx']
  ring

lemma perspective_inverse (l : E →ₗ[ℝ] ℝ) (x : E)
    (hx : denominator l x ≠ 0) :
    perspective (-l) (perspective l x) = x := by
  change (denominator (-l) (perspective l x))⁻¹ •
    ((denominator l x)⁻¹ • x) = x
  rw [denominator_neg_perspective l x hx, inv_inv, smul_smul,
    mul_inv_cancel₀ hx, one_smul]

lemma perspective_mem_opposite_domain (l : E →ₗ[ℝ] ℝ) {x : E}
    (hx : x ∈ positiveDomain l) : perspective l x ∈ positiveDomain (-l) := by
  change 0 < denominator (-l) (perspective l x)
  rw [denominator_neg_perspective l x (ne_of_gt hx)]
  exact inv_pos.mpr hx

lemma perspective_injOn (l : E →ₗ[ℝ] ℝ) :
    Set.InjOn (perspective l) (positiveDomain l) := by
  intro x hx y hy he
  have hback := congrArg (perspective (-l)) he
  rwa [perspective_inverse l x (ne_of_gt hx),
    perspective_inverse l y (ne_of_gt hy)] at hback

/-- Explicit reweighting identity. Positivity is handled in the segment lemmas. -/
lemma perspective_mix (l : E →ₗ[ℝ] ℝ) (x y : E) (a b : ℝ)
    (hx : denominator l x ≠ 0) (hy : denominator l y ≠ 0)
    (hz : denominator l (a • x + b • y) ≠ 0) :
    perspective l (a • x + b • y) =
      (a * denominator l x / denominator l (a • x + b • y)) • perspective l x +
      (b * denominator l y / denominator l (a • x + b • y)) • perspective l y := by
  simp only [perspective, smul_add, smul_smul]
  congr 1
  · congr 1
    field_simp [hx, hz]
  · congr 1
    field_simp [hy, hz]

lemma perspective_mem_segment (l : E →ₗ[ℝ] ℝ) {x y z : E}
    (hx : x ∈ positiveDomain l) (hy : y ∈ positiveDomain l)
    (hz : z ∈ segment ℝ x y) :
    perspective l z ∈ segment ℝ (perspective l x) (perspective l y) := by
  rcases hz with ⟨a, b, ha, hb, hab, rfl⟩
  have hd : 0 < denominator l (a • x + b • y) := by
    rw [denominator_mix l x y a b hab]
    exact weighted_pos ha hb hab hx hy
  refine ⟨a * denominator l x / denominator l (a • x + b • y),
    b * denominator l y / denominator l (a • x + b • y),
    div_nonneg (mul_nonneg ha (le_of_lt hx)) hd.le,
    div_nonneg (mul_nonneg hb (le_of_lt hy)) hd.le, ?_, ?_⟩
  · rw [← add_div, ← denominator_mix l x y a b hab, div_self (ne_of_gt hd)]
  · exact (perspective_mix l x y a b (ne_of_gt hx) (ne_of_gt hy) (ne_of_gt hd)).symm

lemma perspective_mem_openSegment (l : E →ₗ[ℝ] ℝ) {x y z : E}
    (hx : x ∈ positiveDomain l) (hy : y ∈ positiveDomain l)
    (hz : z ∈ openSegment ℝ x y) :
    perspective l z ∈ openSegment ℝ (perspective l x) (perspective l y) := by
  rcases hz with ⟨a, b, ha, hb, hab, rfl⟩
  have hd : 0 < denominator l (a • x + b • y) := by
    rw [denominator_mix l x y a b hab]
    exact weighted_pos ha.le hb.le hab hx hy
  refine ⟨a * denominator l x / denominator l (a • x + b • y),
    b * denominator l y / denominator l (a • x + b • y),
    div_pos (mul_pos ha hx) hd, div_pos (mul_pos hb hy) hd, ?_, ?_⟩
  · rw [← add_div, ← denominator_mix l x y a b hab, div_self (ne_of_gt hd)]
  · exact (perspective_mix l x y a b (ne_of_gt hx) (ne_of_gt hy) (ne_of_gt hd)).symm

lemma perspective_image_segment (l : E →ₗ[ℝ] ℝ) {x y : E}
    (hx : x ∈ positiveDomain l) (hy : y ∈ positiveDomain l) :
    perspective l '' segment ℝ x y =
      segment ℝ (perspective l x) (perspective l y) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact perspective_mem_segment l hx hy hz
  · intro z hz
    have hx' := perspective_mem_opposite_domain l hx
    have hy' := perspective_mem_opposite_domain l hy
    have hz' : z ∈ positiveDomain (-l) :=
      (positiveDomain_convex (-l)).segment_subset hx' hy' hz
    have hpre := perspective_mem_segment (-l) hx' hy' hz
    rw [perspective_inverse l x (ne_of_gt hx),
      perspective_inverse l y (ne_of_gt hy)] at hpre
    refine ⟨perspective (-l) z, hpre, ?_⟩
    simpa only [neg_neg] using perspective_inverse (-l) z (ne_of_gt hz')

lemma perspective_image_openSegment (l : E →ₗ[ℝ] ℝ) {x y : E}
    (hx : x ∈ positiveDomain l) (hy : y ∈ positiveDomain l) :
    perspective l '' openSegment ℝ x y =
      openSegment ℝ (perspective l x) (perspective l y) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact perspective_mem_openSegment l hx hy hz
  · intro z hz
    have hx' := perspective_mem_opposite_domain l hx
    have hy' := perspective_mem_opposite_domain l hy
    have hz' : z ∈ positiveDomain (-l) :=
      (positiveDomain_convex (-l)).segment_subset hx' hy'
        (openSegment_subset_segment ℝ _ _ hz)
    have hpre := perspective_mem_openSegment (-l) hx' hy' hz
    rw [perspective_inverse l x (ne_of_gt hx),
      perspective_inverse l y (ne_of_gt hy)] at hpre
    refine ⟨perspective (-l) z, hpre, ?_⟩
    simpa only [neg_neg] using perspective_inverse (-l) z (ne_of_gt hz')

/-- The projective chart, with all segment identities proved explicitly. -/
theorem perspective_segmentChart (l : E →ₗ[ℝ] ℝ) :
    Hirsch.SegmentChart (positiveDomain l) (perspective l) := by
  refine ⟨positiveDomain_convex l, perspective_injOn l, ?_, ?_⟩
  · intro x hx y hy
    exact perspective_image_segment l hx hy
  · intro x hx y hy
    exact perspective_image_openSegment l hx hy

/-- Every ordinary-edge diameter bound transports at exactly the same budget. -/
theorem perspective_diamLE_image (l : E →ₗ[ℝ] ℝ) (P : Set E)
    (hP : P ⊆ positiveDomain l) (B : ℕ) (hdiam : Hirsch.DiamLE P B) :
    Hirsch.DiamLE (perspective l '' P) B :=
  (perspective_segmentChart l).diamLE_image P hP B hdiam

#print axioms denominator_neg_perspective
#print axioms perspective_inverse
#print axioms perspective_mix
#print axioms perspective_segmentChart
#print axioms perspective_diamLE_image
end HirschPerspective
