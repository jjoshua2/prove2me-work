import Solutions.PolynomialFacePreservingCheckpoints

open Set

noncomputable section

namespace HirschRadial

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Retraction toward one fixed feasible centre. The scale will be the maximum
of 1 and the normalized final-cut violations, never a stage-dependent scale. -/
def point (o x : E) (μ : ℝ) : E := o + μ⁻¹ • (x - o)

lemma eval_point (f : E →ₗ[ℝ] ℝ) (o x : E) (μ : ℝ) :
    f (point o x μ) = f o + μ⁻¹ * (f x - f o) := by
  simp [point]

lemma point_mem_convex (Q : Set E) (hQ : Convex ℝ Q)
    {o x : E} (ho : o ∈ Q) (hx : x ∈ Q) {μ : ℝ} (hμ : 1 ≤ μ) :
    point o x μ ∈ Q := by
  have hpos : 0 < μ := lt_of_lt_of_le zero_lt_one hμ
  have hi : 0 ≤ μ⁻¹ := inv_nonneg.mpr hpos.le
  have hiμ : μ⁻¹ * μ = 1 := inv_mul_cancel₀ hpos.ne'
  have hi1 : μ⁻¹ ≤ 1 := by
    nlinarith [mul_nonneg hi (sub_nonneg.mpr hμ)]
  have h := hQ ho hx (sub_nonneg.mpr hi1) hi (by ring : (1 - μ⁻¹) + μ⁻¹ = 1)
  have heq : (1 - μ⁻¹) • o + μ⁻¹ • x = point o x μ := by
    dsimp [point]
    module
  rwa [heq] at h

lemma point_satisfies_cut (f : E →ₗ[ℝ] ℝ) (b : ℝ) (o x : E)
    {μ : ℝ} (hμ : 1 ≤ μ) (hbound : f x - f o ≤ μ * (b - f o)) :
    f (point o x μ) ≤ b := by
  have hpos : 0 < μ := lt_of_lt_of_le zero_lt_one hμ
  have h := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hpos.le)
  rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul] at h
  rw [eval_point]
  linarith

lemma point_on_active_cut (f : E →ₗ[ℝ] ℝ) (b : ℝ) (o x : E)
    {μ : ℝ} (hμ : 1 ≤ μ) (hactive : f x - f o = μ * (b - f o)) :
    f (point o x μ) = b := by
  have hpos : 0 < μ := lt_of_lt_of_le zero_lt_one hμ
  rw [eval_point, hactive, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  ring

lemma point_at_unit_scale (o x : E) : point o x 1 = x := by
  simp [point]

/-- The largest normalized violation is attained, including the no-cut case.
This uses a maximum over an augmented finite family containing the constant 1. -/
theorem finite_radial_scale_exists {ι : Type*} [Fintype ι] (r : ι → ℝ) :
    ∃ μ : ℝ, 1 ≤ μ ∧ (∀ i, r i ≤ μ) ∧ (μ = 1 ∨ ∃ i, μ = r i) := by
  classical
  let s : Finset ℝ := insert 1 (Finset.univ.image r)
  have hne : s.Nonempty := ⟨1, by simp [s]⟩
  refine ⟨s.max' hne, Finset.le_max' s 1 (by simp [s]), ?_, ?_⟩
  · intro i
    apply Finset.le_max'
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨i, by simp, rfl⟩))
  · have hm := Finset.max'_mem s hne
    rcases Finset.mem_insert.mp hm with h | h
    · exact Or.inl h
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
      exact Or.inr ⟨i, hi.symm⟩

/-- Normalized dominance gives a point of the final clipped parent.
Strict final-cut slack is explicit; no moving-stage face is used. -/
theorem point_mem_final_clip {ι : Type*}
    (Q : Set E) (hQ : Convex ℝ Q) (f : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (o x : E) (ho : o ∈ Q) (hx : x ∈ Q)
    (hstrict : ∀ i, f i o < b i) {μ : ℝ} (hμ : 1 ≤ μ)
    (hmax : ∀ i, (f i x - f i o) / (b i - f i o) ≤ μ) :
    point o x μ ∈ Q ∩ {y | ∀ i, f i y ≤ b i} := by
  refine ⟨point_mem_convex Q hQ ho hx hμ, ?_⟩
  intro i
  apply point_satisfies_cut (f i) (b i) o x hμ
  exact (div_le_iff₀ (sub_pos.mpr (hstrict i))).mp (hmax i)

/-- The active row really is a final supporting face, not merely a label. -/
theorem point_mem_active_final_face (f : E →ₗ[ℝ] ℝ) (b : ℝ) (o x : E)
    (hstrict : f o < b) {μ : ℝ} (hμ : 1 ≤ μ)
    (hactive : μ = (f x - f o) / (b - f o)) :
    f (point o x μ) = b := by
  apply point_on_active_cut f b o x hμ
  rw [hactive, div_mul_cancel₀ _ (sub_pos.mpr hstrict).ne']

/-- An affine dominance inequality checked at both ends holds throughout a
cell. This is why the exact checker certifies whole cells, not sampled points. -/
theorem affine_dominance_on_cell {a₀ a₁ b₀ b₁ t : ℝ}
    (h0 : a₀ ≤ b₀) (h1 : a₁ ≤ b₁) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * a₀ + t * a₁ ≤ (1 - t) * b₀ + t * b₁ := by
  exact add_le_add (mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr ht1))
    (mul_le_mul_of_nonneg_left h1 ht0)

#print axioms eval_point
#print axioms point_mem_convex
#print axioms point_satisfies_cut
#print axioms point_on_active_cut
#print axioms point_at_unit_scale
#print axioms finite_radial_scale_exists
#print axioms point_mem_final_clip
#print axioms point_mem_active_final_face
#print axioms affine_dominance_on_cell

end HirschRadial
