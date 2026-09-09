import Solutions.PolynomialClippingAttachments

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section
namespace HirschRadial

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- Assemble the radial images of two endpoint attachments and one outer walk.
The attachments add no support cost beyond the existing final-cut family. -/
theorem clip_route_with_attachments
    (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (hP : IsCompact (finalClip Q f b))
    (B : ι → ℕ) (hB : ∀ i, DiamLE (finalClip Q f b ∩ {x | f i x = b i}) (B i))
    (u v : ClipSpace d)
    (hu : u ∈ extremePoints ℝ (finalClip Q f b))
    (hv : v ∈ extremePoints ℝ (finalClip Q f b))
    (w : ℕ → ClipSpace d) (L : ℕ) (h0Q : w 0 ∈ extremePoints ℝ Q)
    (hsteps : ∀ k < L, w k = w (k + 1) ∨ Adj Q (w k) (w (k + 1)))
    (hAu : u = w 0 ∨ ∀ x ∈ segment ℝ u (w 0),
      ∃ i, retract f b o x ∈ finalClip Q f b ∧ f i (retract f b o x) = b i)
    (hAv : v = w L ∨ ∀ x ∈ segment ℝ v (w L),
      ∃ i, retract f b o x ∈ finalClip Q f b ∧ f i (retract f b o x) = b i) :
    HirschRegionRoute.Route (Adj (finalClip Q f b)) (L + ∑ i, B i) u v := by
  classical
  let P := finalClip Q f b
  let E : Option (Fin L) → Set (ClipSpace d) :=
    Option.elim (P ∩ {w 0}) (fun k =>
      if Adj Q (w k) (w (k + 1)) then P ∩ segment ℝ (w k) (w (k + 1)) else ∅)
  let F : Sum (Option (Fin L)) ι → Set (ClipSpace d) :=
    Sum.elim E (fun i => P ∩ {x | f i x = b i})
  let C : Sum (Option (Fin L)) ι → ℕ :=
    Sum.elim (fun k => k.elim 0 (fun _ => 1)) B
  have hPc : Convex ℝ P := finalClip_convex Q hQ f b
  have hOld : ∀ k : Option (Fin L),
      IsExtreme ℝ P (E k) ∧ IsClosed (E k) ∧ DiamLE (E k) (k.elim 0 (fun _ => 1)) := by
    intro k
    cases k with
    | none =>
      have hS : IsExtreme ℝ Q {w 0} := isExtreme_singleton.mpr h0Q
      refine ⟨⟨inter_subset_left, ?_⟩, hP.isClosed.inter isClosed_singleton, ?_⟩
      · intro x hx y hy z hz hseg
        exact ⟨hx, hS.left_mem_of_mem_openSegment hx.1 hy.1 hz.2 hseg⟩
      · intro x hx y hy
        have he : x = y := (show x = w 0 from hx.1.2).trans (show y = w 0 from hy.1.2).symm
        exact ⟨fun _ => x, rfl, he, by intro k hk; omega⟩
    | some k =>
      by_cases h : Adj Q (w k) (w (k + 1))
      · simpa [E, h] using clipped_segment_face P Q (fun _ hx => hx.1) hP hPc (w k) (w (k + 1)) h.2
      · have he : IsExtreme ℝ P (∅ : Set (ClipSpace d)) :=
          ⟨empty_subset _, by intro x hx y hy z hz; exact False.elim hz⟩
        have hd : DiamLE (∅ : Set (ClipSpace d)) 1 := by
          intro x hx
          exact False.elim hx.1
        simpa [E, h] using (show IsExtreme ℝ P (∅ : Set (ClipSpace d)) ∧
          IsClosed (∅ : Set (ClipSpace d)) ∧ DiamLE (∅ : Set (ClipSpace d)) 1 from ⟨he, isClosed_empty, hd⟩)
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
  have hMidQ : ∀ x ∈ edgeTrace w L, x ∈ Q := by
    intro x hx
    rcases edgeTrace_edge_or_start Q w L hsteps hx with he | ⟨k, hk, hE, hx⟩
    · exact he.symm ▸ h0Q.1
    · exact hE.2.subset hx
  have hMidCover : ∀ x ∈ edgeTrace w L, ∃ k, retract f b o x ∈ F k := by
    intro x hx
    have hyP := retract_mem Q hQ f b o x ho (hMidQ x hx) hs
    rcases retract_eq_self_or_on_cut f b o x hs with he | ⟨i, hi⟩
    · rcases edgeTrace_edge_or_start Q w L hsteps hx with hx0 | ⟨k, hk, hE, hxE⟩
      · exact ⟨.inl none, hyP, he.trans hx0⟩
      · refine ⟨.inl (some ⟨k, hk⟩), ?_⟩
        change retract f b o x ∈ if Adj Q (w k) (w (k + 1)) then P ∩ segment ℝ (w k) (w (k + 1)) else ∅
        rw [if_pos hE]
        exact ⟨hyP, he.symm ▸ hxE⟩
    · exact ⟨.inr i, hyP, hi⟩
  let K := (segment ℝ u (w 0) ∪ edgeTrace w L) ∪ segment ℝ (w L) v
  have hK : IsPreconnected K :=
    ((convex_segment ℝ u (w 0)).isPreconnected.union'
      ⟨w 0, right_mem_segment ℝ _ _, edgeTrace_start w L⟩ (edgeTrace_preconnected w L)).union'
      ⟨w L, Or.inr (edgeTrace_end w L), left_mem_segment ℝ _ _⟩
      (convex_segment ℝ (w L) v).isPreconnected
  let T := retract f b o '' K
  have hT : IsPreconnected T := hK.image _ (continuous_retract f b o).continuousOn
  have hCover : ∀ y ∈ T, ∃ k, y ∈ F k := by
    rintro y ⟨x, hx, rfl⟩
    rcases hx with (hx | hx) | hx
    · rcases hAu with he | hAu
      · have hx0 : x = w 0 := by simpa [he] using hx
        exact hMidCover x (hx0.symm ▸ edgeTrace_start w L)
      · obtain ⟨i, hi, he⟩ := hAu x hx
        exact ⟨.inr i, hi, he⟩
    · exact hMidCover x hx
    · rcases hAv with he | hAv
      · have hxL : x = w L := by simpa [he] using hx
        exact hMidCover x (hxL.symm ▸ edgeTrace_end w L)
      · have hx' : x ∈ segment ℝ v (w L) := by rwa [segment_symm]
        obtain ⟨i, hi, he⟩ := hAv x hx'
        exact ⟨.inr i, hi, he⟩
  have huT : u ∈ T :=
    ⟨u, Or.inl (Or.inl (left_mem_segment ℝ _ _)), retract_fixes Q f b o u hs hu.1⟩
  have hvT : v ∈ T :=
    ⟨v, Or.inr (right_mem_segment ℝ _ _), retract_fixes Q f b o v hs hv.1⟩
  have hr := HirschRegionRoute.route_of_preconnected_closed_face_cover
    P F C hP hFace hClosed hDiam T hT hCover u v huT hvT hu hv
  simpa [C, Fintype.sum_sum_type, Fintype.sum_option] using hr

/-- Full diameter transfer under simultaneous clipping. Unlike the old-walk
version, neither final endpoint has to remain an outer vertex. Attachments are
constructed from actual maximizing outer vertices, not assumed as portals.
Every final cut face is charged only once across both attachments and the walk. -/
theorem simultaneous_clip_diameter
    (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q) (hQc : IsCompact Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (D : ℕ) (hD : DiamLE Q D)
    (B : ι → ℕ) (hB : ∀ i, DiamLE (finalClip Q f b ∩ {x | f i x = b i}) (B i)) :
    DiamLE (finalClip Q f b) (D + ∑ i, B i) := by
  have hCuts : IsClosed {x : ClipSpace d | ∀ i, f i x ≤ b i} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun i => isClosed_le (f i).continuous continuous_const
  have hP : IsCompact (finalClip Q f b) := hQc.inter_right hCuts
  intro u hu v hv
  obtain ⟨a, ha, hAu⟩ := final_vertex_attachment Q hQ hQc f b o ho hs u hu
  obtain ⟨c, hc, hAv⟩ := final_vertex_attachment Q hQ hQc f b o ho hs v hv
  obtain ⟨w, hw0, hwD, hwsteps⟩ := hD a ha c hc
  apply clip_route_with_attachments Q hQ f b o ho hs hP B hB u v hu hv w D
  · simpa only [hw0] using ha
  · exact hwsteps
  · simpa only [hw0] using hAu
  · simpa only [hwD] using hAv

#print axioms clip_route_with_attachments
#print axioms simultaneous_clip_diameter

end HirschRadial
