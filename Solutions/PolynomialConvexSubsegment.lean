import Solutions.PolynomialFacePreservingCheckpoints

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschSubsegment

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def linePoint (p q : E) (t : ℝ) : E := (1 - t) • p + t • q

lemma linePoint_combo (p q : E) (a b t : ℝ) :
    (1 - t) • linePoint p q a + t • linePoint p q b =
      linePoint p q ((1 - t) * a + t * b) := by
  simp only [linePoint]
  module

lemma linePoint_mem_segment (p q : E) {a b c : ℝ}
    (hab : a < b) (ha : a ≤ c) (hb : c ≤ b) :
    linePoint p q c ∈ segment ℝ (linePoint p q a) (linePoint p q b) := by
  let t : ℝ := (c - a) / (b - a)
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr ha) (sub_pos.mpr hab).le
  have ht1 : t ≤ 1 := (div_le_iff₀ (sub_pos.mpr hab)).mpr (by linarith)
  have hmul : t * (b - a) = c - a := div_mul_cancel₀ _ (sub_pos.mpr hab).ne'
  have hparam : (1 - t) * a + t * b = c := by nlinarith
  refine ⟨1 - t, t, sub_nonneg.mpr ht1, ht0, by ring, ?_⟩
  rw [linePoint_combo, hparam]

lemma linePoint_mem_openSegment (p q : E) {a b c : ℝ}
    (ha : a < c) (hb : c < b) :
    linePoint p q c ∈ openSegment ℝ (linePoint p q a) (linePoint p q b) := by
  have hab : a < b := ha.trans hb
  let t : ℝ := (c - a) / (b - a)
  have ht0 : 0 < t := div_pos (sub_pos.mpr ha) (sub_pos.mpr hab)
  have ht1 : t < 1 := (div_lt_iff₀ (sub_pos.mpr hab)).mpr (by linarith)
  have hmul : t * (b - a) = c - a := div_mul_cancel₀ _ (sub_pos.mpr hab).ne'
  have hparam : (1 - t) * a + t * b = c := by nlinarith
  refine ⟨1 - t, t, sub_pos.mpr ht1, ht0, by ring, ?_⟩
  rw [linePoint_combo, hparam]

lemma segment_point_parameter (p q : E) {x : E} (hx : x ∈ segment ℝ p q) :
    ∃ t : ℝ, linePoint p q t = x := by
  obtain ⟨a, b, _, _, hab, hx⟩ := hx
  refine ⟨b, ?_⟩
  have ha : a = 1 - b := by linarith
  simpa [linePoint, ha] using hx

lemma subset_of_ordered_extreme_parameters (S : Set E) (p q : E)
    (hsub : S ⊆ segment ℝ p q) {a b : ℝ} (hab : a < b)
    (ha : linePoint p q a ∈ extremePoints ℝ S)
    (hb : linePoint p q b ∈ extremePoints ℝ S)
    (hne : linePoint p q a ≠ linePoint p q b) :
    S ⊆ segment ℝ (linePoint p q a) (linePoint p q b) := by
  intro z hz
  obtain ⟨c, hc⟩ := segment_point_parameter p q (hsub hz)
  have hz' : linePoint p q c ∈ S := hc.symm ▸ hz
  have hac : a ≤ c := by
    by_contra h
    have hca : c < a := lt_of_not_ge h
    have hop := linePoint_mem_openSegment p q hca hab
    have hba : linePoint p q b = linePoint p q a :=
      ha.2 hb.1 hz' (by rw [openSegment_symm]; exact hop)
    exact hne hba.symm
  have hcb : c ≤ b := by
    by_contra h
    have hbc : b < c := lt_of_not_ge h
    exact hne (hb.2 ha.1 hz' (linePoint_mem_openSegment p q hab hbc))
  exact hc ▸ linePoint_mem_segment p q hab hac hcb

/-- Every convex subset of a segment has graph diameter at most one. -/
theorem diamLE_of_convex_subsegment
    (S : Set E) (hS : Convex ℝ S) (p q : E) (hsub : S ⊆ segment ℝ p q) :
    DiamLE S 1 := by
  intro u hu v hv
  by_cases huv : u = v
  · subst v
    exact ⟨fun _ => u, rfl, rfl, fun _ _ => Or.inl rfl⟩
  obtain ⟨a, ha⟩ := segment_point_parameter p q (hsub hu.1)
  obtain ⟨b, hb⟩ := segment_point_parameter p q (hsub hv.1)
  have hab : a ≠ b := by
    intro h
    exact huv (ha.symm.trans ((congrArg (linePoint p q) h).trans hb))
  have hsub' : S ⊆ segment ℝ u v := by
    rcases lt_or_gt_of_ne hab with h | h
    · simpa [ha, hb] using subset_of_ordered_extreme_parameters S p q hsub h
        (ha.symm ▸ hu) (hb.symm ▸ hv) (by simpa [ha, hb] using huv)
    · have h' := subset_of_ordered_extreme_parameters S p q hsub h
        (hb.symm ▸ hv) (ha.symm ▸ hu) (by simpa [ha, hb] using huv.symm)
      simpa [ha, hb, segment_symm] using h'
  have heq : segment ℝ u v = S := (hS.segment_subset hu.1 hv.1).antisymm hsub'
  have hadj : Adj S u v := ⟨huv, by rw [heq]; exact IsExtreme.rfl⟩
  exact HirschRegionRoute.route_one (Adj S) (Or.inr hadj)

lemma extreme_inter_of_parent_subset (Q P F : Set E)
    (hPQ : P ⊆ Q) (hF : IsExtreme ℝ Q F) :
    IsExtreme ℝ P (P ∩ F) := by
  refine ⟨inter_subset_left, ?_⟩
  intro x hx y hy z hz hseg
  exact ⟨hx, hF.left_mem_of_mem_openSegment (hPQ hx) (hPQ hy) hz.2 hseg⟩

#print axioms linePoint_combo
#print axioms linePoint_mem_segment
#print axioms linePoint_mem_openSegment
#print axioms segment_point_parameter
#print axioms subset_of_ordered_extreme_parameters
#print axioms diamLE_of_convex_subsegment
#print axioms extreme_inter_of_parent_subset

end HirschSubsegment
