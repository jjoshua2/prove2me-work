import Solutions.PolynomialClippingDiameter

/-! Exterior-cap shortcuts for simultaneous clipping.

The cap is a genuine convex subset of the compact truncated outer parent and
is disjoint from the FINAL polytope. All cap motion retracts to the already
charged final cut faces. No diameter budget for the cap is assumed.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRadial HirschRegionRoute

noncomputable section
namespace HirschExterior

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- Any outer point absent from the final clip retracts to a final cut face. -/
lemma retract_on_cut_of_exterior
    (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (x : ClipSpace d) (hx : x ∈ Q) (hout : x ∉ finalClip Q f b) :
    ∃ i, retract f b o x ∈ finalClip Q f b ∧ f i (retract f b o x) = b i := by
  have hy := retract_mem Q hQ f b o x ho hx hs
  rcases retract_eq_self_or_on_cut f b o x hs with he | ⟨i, hi⟩
  · exact False.elim (hout (he ▸ hy))
  · exact ⟨i, hy, hi⟩

/-- A convex exterior cap gives genuine connected traces on the union of
final cut faces, with no intrinsic cap-diameter assumption. -/
theorem exterior_cap_trace
    (Q G : Set (ClipSpace d)) (hQ : Convex ℝ Q) (hG : Convex ℝ G)
    (hGQ : G ⊆ Q) (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (hout : ∀ x ∈ G, x ∉ finalClip Q f b) :
    IsPreconnected (retract f b o '' G) ∧
      ∀ y ∈ retract f b o '' G,
        ∃ i, y ∈ finalClip Q f b ∩ {x | f i x = b i} := by
  refine ⟨hG.isPreconnected.image _ (continuous_retract f b o).continuousOn, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact retract_on_cut_of_exterior Q hQ f b o ho hs x (hGQ hx) (hout x hx)

/-- An exterior jump may be a long segment in the cap. Stays add no new
points; other trace points belong to genuine outer edges or to the cap. -/
lemma exterior_edgeTrace_cases
    (Q G : Set (ClipSpace d)) (hG : Convex ℝ G)
    (w : ℕ → ClipSpace d) (L : ℕ)
    (hsteps : ∀ k < L, w k = w (k + 1) ∨
      Adj Q (w k) (w (k + 1)) ∨ (w k ∈ G ∧ w (k + 1) ∈ G))
    {x : ClipSpace d} (hx : x ∈ edgeTrace w L) :
    x = w 0 ∨ (∃ k < L, Adj Q (w k) (w (k + 1)) ∧
      x ∈ segment ℝ (w k) (w (k + 1))) ∨ x ∈ G := by
  induction L with
  | zero => exact Or.inl hx
  | succ L ih =>
    have hp : ∀ k < L, w k = w (k + 1) ∨
        Adj Q (w k) (w (k + 1)) ∨ (w k ∈ G ∧ w (k + 1) ∈ G) :=
      fun k hk => hsteps k (by omega)
    have lift : x = w 0 ∨ (∃ k < L, Adj Q (w k) (w (k + 1)) ∧
        x ∈ segment ℝ (w k) (w (k + 1))) ∨ x ∈ G →
        x = w 0 ∨ (∃ k < L + 1, Adj Q (w k) (w (k + 1)) ∧
        x ∈ segment ℝ (w k) (w (k + 1))) ∨ x ∈ G := by
      rintro (h | ⟨k, hk, he, hx⟩ | hg)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨k, by omega, he, hx⟩)
      · exact Or.inr (Or.inr hg)
    rcases hx with hx | hx
    · exact lift (ih hp hx)
    · rcases hsteps L (by omega) with he | hE | hcap
      · have hx' : x = w L := by simpa [← he] using hx
        exact lift (ih hp (hx'.symm ▸ edgeTrace_end w L))
      · exact Or.inr (Or.inl ⟨L, by omega, hE, hx⟩)
      · exact Or.inr (Or.inr (hG.segment_subset hcap.1 hcap.2 hx))

/-- Full endpoint-attachment assembly allowing arbitrary shortcuts inside one
convex exterior cap. Only genuine edges supply clipped-edge supports. The
cap itself is never a paid region of the final parent. -/
theorem clip_route_with_exterior_attachments
    (Q G : Set (ClipSpace d)) (hQ : Convex ℝ Q) (hG : Convex ℝ G) (hGQ : G ⊆ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (hP : IsCompact (finalClip Q f b))
    (hout : ∀ x ∈ G, x ∉ finalClip Q f b)
    (B : ι → ℕ) (hB : ∀ i, DiamLE (finalClip Q f b ∩ {x | f i x = b i}) (B i))
    (u v : ClipSpace d)
    (hu : u ∈ extremePoints ℝ (finalClip Q f b))
    (hv : v ∈ extremePoints ℝ (finalClip Q f b))
    (w : ℕ → ClipSpace d) (L : ℕ) (h0Q : w 0 ∈ extremePoints ℝ Q)
    (hsteps : ∀ k < L, w k = w (k + 1) ∨
      Adj Q (w k) (w (k + 1)) ∨ (w k ∈ G ∧ w (k + 1) ∈ G))
    (hAu : u = w 0 ∨ ∀ x ∈ segment ℝ u (w 0),
      ∃ i, retract f b o x ∈ finalClip Q f b ∧ f i (retract f b o x) = b i)
    (hAv : v = w L ∨ ∀ x ∈ segment ℝ v (w L),
      ∃ i, retract f b o x ∈ finalClip Q f b ∧ f i (retract f b o x) = b i) :
    Route (Adj (finalClip Q f b)) (L + ∑ i, B i) u v := by
  classical
  let P := finalClip Q f b
  let E : Option (Fin L) → Set (ClipSpace d) := fun k =>
    k.elim (P ∩ {w 0}) (fun k =>
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
    rcases exterior_edgeTrace_cases Q G hG w L hsteps hx with he | ⟨k, hk, hE, hx⟩ | hxG
    · exact he.symm ▸ h0Q.1
    · exact hE.2.subset hx
    · exact hGQ hxG
  have hMidCover : ∀ x ∈ edgeTrace w L, ∃ k, retract f b o x ∈ F k := by
    intro x hx
    have hyP := retract_mem Q hQ f b o x ho (hMidQ x hx) hs
    rcases retract_eq_self_or_on_cut f b o x hs with he | ⟨i, hi⟩
    · rcases exterior_edgeTrace_cases Q G hG w L hsteps hx with hx0 | ⟨k, hk, hE, hxE⟩ | hxG
      · exact ⟨.inl none, hyP, he.trans hx0⟩
      · refine ⟨.inl (some ⟨k, hk⟩), ?_⟩
        change retract f b o x ∈ if Adj Q (w k) (w (k + 1)) then P ∩ segment ℝ (w k) (w (k + 1)) else ∅
        rw [if_pos hE]
        exact ⟨hyP, he.symm ▸ hxE⟩
      · exact False.elim (hout x hxG (he ▸ hyP))
    · exact ⟨.inr i, hyP, hi⟩
  let K := (segment ℝ u (w 0) ∪ edgeTrace w L) ∪ segment ℝ (w L) v
  have hK : IsPreconnected K :=
    ((convex_segment u (w 0)).isPreconnected.union'
      ⟨w 0, right_mem_segment ℝ _ _, edgeTrace_start w L⟩ (edgeTrace_preconnected w L)).union'
      ⟨w L, Or.inr (edgeTrace_end w L), left_mem_segment ℝ _ _⟩
      (convex_segment (w L) v).isPreconnected
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
  have hr := route_of_preconnected_closed_face_cover
    P F C hP hFace hClosed hDiam T hT hCover u v huT hvT hu hv
  simpa [C, Fintype.sum_sum_type, Fintype.sum_option] using hr

/-- Diameter transfer using actual outer edges and convex exterior-cap
shortcuts. New final vertices are lifted by compact optimization, not assumed
already connected. No cap-diameter budget occurs in the conclusion. -/
theorem clip_diameter_from_exterior_routes
    (Q G : Set (ClipSpace d)) (hQ : Convex ℝ Q) (hQc : IsCompact Q)
    (hG : Convex ℝ G) (hGQ : G ⊆ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (hout : ∀ x ∈ G, x ∉ finalClip Q f b)
    (D : ℕ)
    (hD : ∀ a ∈ extremePoints ℝ Q, ∀ c ∈ extremePoints ℝ Q,
      Route (fun x y => Adj Q x y ∨ (x ∈ G ∧ y ∈ G)) D a c)
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
  apply clip_route_with_exterior_attachments Q G hQ hG hGQ f b o ho hs hP hout B hB u v hu hv w D
  · simpa only [hw0] using ha
  · exact hwsteps
  · simpa only [hw0] using hAu
  · simpa only [hwD] using hAv

/-- The structural cap condition adds at most ONE step. Both cap endpoints
can be connected directly through the cap, so two ray charges are unnecessary. -/
theorem exterior_cap_augmented_route_bound
    (Q G V : Set (ClipSpace d)) (D : ℕ)
    (hOld : ∀ a ∈ V, ∀ c ∈ V, Route (Adj Q) D a c)
    (hclass : ∀ x ∈ extremePoints ℝ Q,
      x ∈ V ∨ (x ∈ G ∧ ∃ a ∈ V, Adj Q a x)) :
    ∀ u ∈ extremePoints ℝ Q, ∀ v ∈ extremePoints ℝ Q,
      Route (fun x y => Adj Q x y ∨ (x ∈ G ∧ y ∈ G)) (D + 1) u v := by
  let R := fun x y => Adj Q x y ∨ (x ∈ G ∧ y ∈ G)
  have hOldR : ∀ a ∈ V, ∀ c ∈ V, Route R D a c := by
    intro a ha c hc
    obtain ⟨w, h0, hD, hsteps⟩ := hOld a ha c hc
    refine ⟨w, h0, hD, ?_⟩
    intro k hk
    exact (hsteps k hk).imp id Or.inl
  have pad : ∀ {a c : ClipSpace d} {N : ℕ}, N ≤ D + 1 → Route R N a c → Route R (D + 1) a c := by
    intro a c N hle ⟨w, h0, hN, hs⟩
    exact HirschProduct.pad_walk R hle w h0 hN hs
  have cat : ∀ {a c z : ClipSpace d} {M N : ℕ},
      Route R M a c → Route R N c z → Route R (M + N) a z := by
    intro a c z M N ⟨w, h0, hM, hw⟩ ⟨q, hq0, hqN, hq⟩
    exact HirschProduct.append_walk R w q h0 hM hq0 hqN hw hq
  intro u hu v hv
  rcases hclass u hu with huV | ⟨huG, a, haV, hau⟩
  · rcases hclass v hv with hvV | ⟨hvG, c, hcV, hcv⟩
    · exact pad (by omega) (hOldR u huV v hvV)
    · exact cat (hOldR u huV c hcV) (route_one R (Or.inr (Or.inl hcv)))
  · rcases hclass v hv with hvV | ⟨hvG, c, hcV, hcv⟩
    · have hua : Adj Q u a := ⟨hau.1.symm, by simpa [segment_symm] using hau.2⟩
      have hr := cat (route_one R (Or.inr (Or.inl hua))) (hOldR a haV v hvV)
      simpa [Nat.add_comm] using hr
    · exact pad (by omega) (route_one R (Or.inr (Or.inr ⟨huG, hvG⟩)))

/-- End-to-end cap-witness form of pointed unbounded clipping. A sufficiently
far truncation of a pointed polyhedron has exactly this vertex classification:
old vertices route in D steps; every new cap vertex is adjacent to an old one.
The general polyhedral existence of that truncation is NOT proved in this file.
All final-face costs remain explicit. -/
theorem simultaneous_clip_diameter_from_exterior_cap
    (Q G V : Set (ClipSpace d)) (hQ : Convex ℝ Q) (hQc : IsCompact Q)
    (hG : Convex ℝ G) (hGQ : G ⊆ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (hout : ∀ x ∈ G, x ∉ finalClip Q f b)
    (D : ℕ) (hOld : ∀ a ∈ V, ∀ c ∈ V, Route (Adj Q) D a c)
    (hclass : ∀ x ∈ extremePoints ℝ Q,
      x ∈ V ∨ (x ∈ G ∧ ∃ a ∈ V, Adj Q a x))
    (B : ι → ℕ) (hB : ∀ i, DiamLE (finalClip Q f b ∩ {x | f i x = b i}) (B i)) :
    DiamLE (finalClip Q f b) (D + 1 + ∑ i, B i) := by
  exact clip_diameter_from_exterior_routes Q G hQ hQc hG hGQ f b o ho hs hout
    (D + 1) (exterior_cap_augmented_route_bound Q G V D hOld hclass) B hB

#print axioms retract_on_cut_of_exterior
#print axioms exterior_cap_trace
#print axioms exterior_edgeTrace_cases
#print axioms clip_route_with_exterior_attachments
#print axioms clip_diameter_from_exterior_routes
#print axioms exterior_cap_augmented_route_bound
#print axioms simultaneous_clip_diameter_from_exterior_cap

end HirschExterior
