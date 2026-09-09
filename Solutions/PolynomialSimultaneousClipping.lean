import Solutions.PolynomialContinuousRepair

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRadial

variable {d : ℕ}

lemma segment_collinear (a b : ClipSpace d) : Collinear ℝ (segment ℝ a b) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨a, b - a, ?_⟩
  intro x hx
  obtain ⟨s, t, _, _, hst, rfl⟩ := hx
  refine ⟨t, ?_⟩
  change s • a + t • b = t • (b - a) + a
  have hs : s = 1 - t := by linarith
  rw [hs]
  module

/-- Any convex collinear set has graph diameter at most one, even without
compactness. If it has two distinct extreme points, they span the entire set. -/
theorem diamLE_one_of_convex_collinear
    (S : Set (ClipSpace d)) (hS : Convex ℝ S) (hcol : Collinear ℝ S) : DiamLE S 1 := by
  intro u hu v hv
  by_cases huv : u = v
  · exact HirschRegionRoute.route_one (Adj S) (Or.inl huv)
  have hEq : S = segment ℝ u v := by
    apply Subset.antisymm ?_ (hS.segment_subset hu.1 hv.1)
    intro x hx
    have h3 : Collinear ℝ ({u, x, v} : Set (ClipSpace d)) :=
      hcol.subset (by simp only [insert_subset_iff, singleton_subset_iff]; exact ⟨hu.1, hx, hv.1⟩)
    rcases h3.wbtw_or_wbtw_or_wbtw with h | h | h
    · exact h.mem_segment
    · rcases (mem_extremePoints_iff_forall_segment.mp hv).2 x hx u hu.1 h.mem_segment with h | h
      · simpa [h] using (right_mem_segment ℝ u v)
      · exact False.elim (huv h)
    · rcases (mem_extremePoints_iff_forall_segment.mp hu).2 v hv.1 x hx h.mem_segment with h | h
      · exact False.elim (huv h.symm)
      · simpa [h] using (left_mem_segment ℝ u v)
  apply HirschRegionRoute.route_one (Adj S)
  right
  refine ⟨huv, ?_⟩
  rw [← hEq]
  exact IsExtreme.refl ℝ S

/-- Clipping an old edge produces a closed extreme face of diameter at most
one. The same proof covers a retained singleton and an empty clipped edge. -/
theorem clipped_segment_face
    (P Q : Set (ClipSpace d)) (hPQ : P ⊆ Q) (hP : IsCompact P) (hPc : Convex ℝ P)
    (a b : ClipSpace d) (hE : IsExtreme ℝ Q (segment ℝ a b)) :
    IsExtreme ℝ P (P ∩ segment ℝ a b) ∧
      IsClosed (P ∩ segment ℝ a b) ∧ DiamLE (P ∩ segment ℝ a b) 1 := by
  have hclosed : IsClosed (segment ℝ a b) := by
    rw [segment_eq_image]
    exact (isCompact_Icc.image (by fun_prop)).isClosed
  refine ⟨?_, hP.isClosed.inter hclosed, ?_⟩
  · refine ⟨inter_subset_left, ?_⟩
    intro x hx y hy z hz hseg
    exact ⟨hx, hE.left_mem_of_mem_openSegment (hPQ hx) (hPQ hy) hz.2 hseg⟩
  · exact diamLE_one_of_convex_collinear _ (hPc.inter (convex_segment a b))
      ((segment_collinear a b).subset inter_subset_right)

lemma supporting_cut_extreme
    (P : Set (ClipSpace d)) (f : ClipSpace d →L[ℝ] ℝ) (c : ℝ)
    (hbound : ∀ x ∈ P, f x ≤ c) : IsExtreme ℝ P (P ∩ {x | f x = c}) := by
  refine ⟨inter_subset_left, ?_⟩
  intro x hx y hy z hz hseg
  refine ⟨hx, ?_⟩
  by_contra hne
  have hlt : f x < c := lt_of_le_of_ne (hbound x hx) hne
  obtain ⟨a, b, ha, hb, hab, he⟩ := hseg
  have he' := congrArg f he
  simp only [map_add, map_smul, smul_eq_mul] at he'
  rw [hz.2] at he'
  have hlt' := add_lt_add_of_lt_of_le
    (mul_lt_mul_of_pos_left hlt ha)
    (mul_le_mul_of_nonneg_left (hbound y hy) hb.le)
  rw [← add_mul, hab, one_mul] at hlt'
  linarith

variable {ι : Type*} [Fintype ι]

lemma finalClip_convex (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) : Convex ℝ (finalClip Q f b) := by
  intro x hx y hy a c ha hc hac
  refine ⟨hQ hx.1 hy.1 ha hc hac, ?_⟩
  intro i
  simp only [map_add, map_smul, smul_eq_mul]
  calc
    a * f i x + c * f i y ≤ a * b i + c * b i :=
      add_le_add (mul_le_mul_of_nonneg_left (hx.2 i) ha) (mul_le_mul_of_nonneg_left (hy.2 i) hc)
    _ = b i := by rw [← add_mul, hac, one_mul]

/-- The complete geometric trace of an old walk, including the zero-step case. -/
def edgeTrace (w : ℕ → ClipSpace d) : ℕ → Set (ClipSpace d)
  | 0 => {w 0}
  | L + 1 => edgeTrace w L ∪ segment ℝ (w L) (w (L + 1))

lemma edgeTrace_start (w : ℕ → ClipSpace d) (L : ℕ) : w 0 ∈ edgeTrace w L := by
  induction L with
  | zero => rfl
  | succ L ih => exact Or.inl ih

lemma edgeTrace_end (w : ℕ → ClipSpace d) (L : ℕ) : w L ∈ edgeTrace w L := by
  cases L with
  | zero => rfl
  | succ L => exact Or.inr (right_mem_segment ℝ _ _)

lemma edgeTrace_preconnected (w : ℕ → ClipSpace d) (L : ℕ) :
    IsPreconnected (edgeTrace w L) := by
  induction L with
  | zero => exact isPreconnected_singleton
  | succ L ih =>
    exact ih.union' ⟨w L, edgeTrace_end w L, left_mem_segment ℝ _ _⟩
      (convex_segment _ _).isPreconnected

lemma edgeTrace_cases (w : ℕ → ClipSpace d) (L : ℕ) {x : ClipSpace d}
    (hx : x ∈ edgeTrace w L) : x = w 0 ∨ ∃ k < L, x ∈ segment ℝ (w k) (w (k + 1)) := by
  induction L with
  | zero => exact Or.inl hx
  | succ L ih =>
    rcases hx with hx | hx
    · rcases ih hx with h | ⟨k, hk, hx⟩
      · exact Or.inl h
      · exact Or.inr ⟨k, by omega, hx⟩
    · exact Or.inr ⟨L, by omega, hx⟩

lemma edgeTrace_covered (w : ℕ → ClipSpace d) (L : ℕ) (hL : 0 < L)
    {x : ClipSpace d} (hx : x ∈ edgeTrace w L) :
    ∃ k : Fin L, x ∈ segment ℝ (w k) (w (k + 1)) := by
  rcases edgeTrace_cases w L hx with h | ⟨k, hk, hx⟩
  · exact ⟨⟨0, hL⟩, h ▸ left_mem_segment ℝ _ _⟩
  · exact ⟨⟨k, hk⟩, hx⟩

/-- End-to-end simultaneous clipping. Every final cut face is charged once,
not once per old-edge crossing or deformation event. The old walk may contain
stays. Q need only be convex, P compact, and the centre strictly feasible for
the added cuts. No finite-cell cover is assumed: continuity constructs the
needed connected trace and actual fixed-parent support intersections. -/
theorem simultaneous_clip_route
    (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (hP : IsCompact (finalClip Q f b))
    (B : ι → ℕ) (hB : ∀ i, DiamLE (finalClip Q f b ∩ {x | f i x = b i}) (B i))
    (w : ℕ → ClipSpace d) (L : ℕ)
    (hverts : ∀ k ≤ L, w k ∈ extremePoints ℝ Q)
    (hsteps : ∀ k < L, w k = w (k + 1) ∨ Adj Q (w k) (w (k + 1)))
    (h0 : w 0 ∈ extremePoints ℝ (finalClip Q f b))
    (hL : w L ∈ extremePoints ℝ (finalClip Q f b)) :
    HirschRegionRoute.Route (Adj (finalClip Q f b)) (L + ∑ i, B i) (w 0) (w L) := by
  classical
  by_cases hzero : L = 0
  · subst L
    exact ⟨fun _ => w 0, rfl, rfl, fun _ _ => Or.inl rfl⟩
  have hpos : 0 < L := Nat.pos_of_ne_zero hzero
  let P := finalClip Q f b
  let F : Sum (Fin L) ι → Set (ClipSpace d) :=
    Sum.elim (fun k => P ∩ segment ℝ (w k) (w (k + 1)))
      (fun i => P ∩ {x | f i x = b i})
  let C : Sum (Fin L) ι → ℕ := Sum.elim (fun _ => 1) B
  have hPc : Convex ℝ P := finalClip_convex Q hQ f b
  have hOld : ∀ k : Fin L,
      IsExtreme ℝ P (F (.inl k)) ∧ IsClosed (F (.inl k)) ∧ DiamLE (F (.inl k)) 1 := by
    intro k
    apply clipped_segment_face P Q (fun _ hx => hx.1) hP hPc
    rcases hsteps k k.isLt with h | h
    · rw [h, segment_same]
      exact isExtreme_singleton.mpr (hverts (k + 1) (by omega))
    · exact h.2
  have hFace : ∀ k, IsExtreme ℝ P (F k) := by
    intro k
    cases k with
    | inl k => exact (hOld k).1
    | inr i => exact supporting_cut_extreme P (f i) (b i) (fun x hx => hx.2 i)
  have hClosed : ∀ k, IsClosed (F k) := by
    intro k
    cases k with
    | inl k => exact (hOld k).2.1
    | inr i => exact hP.isClosed.inter (isClosed_eq (f i).continuous continuous_const)
  have hDiam : ∀ k, DiamLE (F k) (C k) := by
    intro k
    cases k with
    | inl k => exact (hOld k).2.2
    | inr i => exact hB i
  have hTraceQ : ∀ x ∈ edgeTrace w L, x ∈ Q := by
    intro x hx
    obtain ⟨k, hk⟩ := edgeTrace_covered w L hpos hx
    exact hQ.segment_subset (hverts k (by omega)).1 (hverts (k + 1) (by omega)).1 hk
  let T := retract f b o '' edgeTrace w L
  have hT : IsPreconnected T :=
    (edgeTrace_preconnected w L).image _ (continuous_retract f b o).continuousOn
  have hCover : ∀ y ∈ T, ∃ k, y ∈ F k := by
    rintro y ⟨x, hx, rfl⟩
    have hyP := retract_mem Q hQ f b o x ho (hTraceQ x hx) hs
    rcases retract_eq_self_or_on_cut f b o x hs with heq | ⟨i, hi⟩
    · obtain ⟨k, hk⟩ := edgeTrace_covered w L hpos hx
      exact ⟨.inl k, hyP, heq.symm ▸ hk⟩
    · exact ⟨.inr i, hyP, hi⟩
  have huT : w 0 ∈ T := ⟨w 0, edgeTrace_start w L, retract_fixes Q f b o (w 0) hs h0.1⟩
  have hvT : w L ∈ T := ⟨w L, edgeTrace_end w L, retract_fixes Q f b o (w L) hs hL.1⟩
  have hr := HirschRegionRoute.route_of_preconnected_closed_face_cover
    P F C hP hFace hClosed hDiam T hT hCover (w 0) (w L) huT hvT h0 hL
  simpa [C, Fintype.sum_sum_type] using hr

#print axioms segment_collinear
#print axioms diamLE_one_of_convex_collinear
#print axioms clipped_segment_face
#print axioms supporting_cut_extreme
#print axioms finalClip_convex
#print axioms edgeTrace_start
#print axioms edgeTrace_end
#print axioms edgeTrace_preconnected
#print axioms edgeTrace_cases
#print axioms edgeTrace_covered
#print axioms simultaneous_clip_route

end HirschRadial
