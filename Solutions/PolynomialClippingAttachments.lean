import Solutions.PolynomialSimultaneousClipping

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section
namespace HirschRadial

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- A vertex strictly inside all added halfspaces was already an outer vertex.
A common small homothety makes both ends of any proposed outer segment feasible. -/
theorem extreme_outer_of_strict_cuts
    (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (x : ClipSpace d)
    (hx : x ∈ extremePoints ℝ (finalClip Q f b))
    (hsx : ∀ i, f i x < b i) : x ∈ extremePoints ℝ Q := by
  refine ⟨hx.1.1, ?_⟩
  intro y hy z hz hopen
  let μ := max (scale f b x y) (scale f b x z)
  have hμ : 1 ≤ μ := (scale_ge_one f b x y).trans (le_max_left _ _)
  have hyP : point x y μ ∈ finalClip Q f b :=
    point_mem_final_clip Q hQ (fun i => (f i).toLinearMap) b x y hx.1.1 hy hsx hμ
      (fun i => (normalized_le_scale f b x y i).trans (le_max_left _ _))
  have hzP : point x z μ ∈ finalClip Q f b :=
    point_mem_final_clip Q hQ (fun i => (f i).toLinearMap) b x z hx.1.1 hz hsx hμ
      (fun i => (normalized_le_scale f b x z i).trans (le_max_right _ _))
  have hopen' : x ∈ openSegment ℝ (point x y μ) (point x z μ) := by
    obtain ⟨a, c, ha, hc, hac, he⟩ := hopen
    refine ⟨a, c, ha, hc, hac, ?_⟩
    dsimp [point]
    calc
      a • (x + μ⁻¹ • (y - x)) + c • (x + μ⁻¹ • (z - x)) =
          (a + c) • x + μ⁻¹ • (a • y + c • z - (a + c) • x) := by module
      _ = x := by rw [hac, one_smul, he]; simp
  have he := hx.2 hyP hzP hopen'
  change x + μ⁻¹ • (y - x) = x at he
  have hsmul : μ⁻¹ • (y - x) = 0 := add_left_cancel (he.trans (add_zero x).symm)
  have hμ0 : μ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hμ)
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsmul).resolve_left (inv_ne_zero hμ0))

/-- Every new vertex lies on an actual final cut. -/
theorem extreme_outer_or_on_final_cut
    (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (x : ClipSpace d)
    (hx : x ∈ extremePoints ℝ (finalClip Q f b)) :
    x ∈ extremePoints ℝ Q ∨ ∃ i, f i x = b i := by
  classical
  by_cases h : ∃ i, f i x = b i
  · exact Or.inr h
  · left
    apply extreme_outer_of_strict_cuts Q hQ f b x hx
    intro i
    have hne : f i x ≠ b i := fun hi => h ⟨i, hi⟩
    exact lt_of_le_of_ne (hx.1.2 i) hne

/-- A linear functional reaches its outer maximum at an outer extreme point. -/
theorem outer_vertex_above
    (Q : Set (ClipSpace d)) (hQ : IsCompact Q)
    (g : ClipSpace d →L[ℝ] ℝ) (x : ClipSpace d) (hx : x ∈ Q) :
    ∃ a, a ∈ extremePoints ℝ Q ∧ g x ≤ g a := by
  obtain ⟨z, hz, hmax⟩ := hQ.exists_isMaxOn ⟨x, hx⟩ g.continuous.continuousOn
  have hF := supporting_cut_extreme Q g (g z) (fun y hy => hmax hy)
  have hFc : IsClosed (Q ∩ {y | g y = g z}) :=
    hQ.isClosed.inter (isClosed_eq g.continuous continuous_const)
  obtain ⟨a, ha, haF⟩ := HirschRegionRoute.compact_face_point_has_parent_vertex
    Q (Q ∩ {y | g y = g z}) hQ hF hFc ⟨z, hz, rfl⟩
  exact ⟨a, ha, (hmax hx).trans_eq haF.2.symm⟩

/-- A segment going outward through one active cut retracts entirely into the
union of final cut faces. The active label may change, but the family is fixed. -/
theorem outward_segment_retract_on_cut
    (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (u a : ClipSpace d) (hu : u ∈ finalClip Q f b) (ha : a ∈ Q)
    (i : ι) (hui : f i u = b i) (hai : b i ≤ f i a)
    (x : ClipSpace d) (hx : x ∈ segment ℝ u a) :
    ∃ j, retract f b o x ∈ finalClip Q f b ∧ f j (retract f b o x) = b j := by
  have hxQ : x ∈ Q := hQ.segment_subset hu.1 ha hx
  have hxP := retract_mem Q hQ f b o x ho hxQ hs
  have hge : b i ≤ f i x := by
    obtain ⟨s, t, hs0, ht0, hst, he⟩ := hx
    have he' := congrArg (f i) he
    simp only [map_add, map_smul, smul_eq_mul] at he'
    rw [hui] at he'
    calc
      b i = (s + t) * b i := by rw [hst, one_mul]
      _ = s * b i + t * b i := add_mul _ _ _
      _ ≤ s * b i + t * f i a :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hai ht0)
      _ = f i x := he'
  rcases retract_eq_self_or_on_cut f b o x hs with he | ⟨j, hj⟩
  · refine ⟨i, hxP, ?_⟩
    rw [he]
    have hle : f i x ≤ b i := by simpa [he] using hxP.2 i
    exact le_antisymm hle hge
  · exact ⟨j, hxP, hj⟩

/-- Every final vertex attaches to the radial image of an outer vertex using
only final cut faces; an already outer vertex needs no attachment at all. -/
theorem final_vertex_attachment
    (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q) (hQc : IsCompact Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o : ClipSpace d) (ho : o ∈ Q) (hs : ∀ i, f i o < b i)
    (u : ClipSpace d) (hu : u ∈ extremePoints ℝ (finalClip Q f b)) :
    ∃ a, a ∈ extremePoints ℝ Q ∧
      (u = a ∨ ∀ x ∈ segment ℝ u a,
        ∃ i, retract f b o x ∈ finalClip Q f b ∧ f i (retract f b o x) = b i) := by
  rcases extreme_outer_or_on_final_cut Q hQ f b u hu with huQ | ⟨i, hi⟩
  · exact ⟨u, huQ, Or.inl rfl⟩
  · obtain ⟨a, ha, hab⟩ := outer_vertex_above Q hQc (f i) u hu.1.1
    refine ⟨a, ha, Or.inr ?_⟩
    intro x hx
    apply outward_segment_retract_on_cut Q hQ f b o ho hs u a hu.1 ha.1 i hi
    · simpa [hi] using hab
    · exact hx

/-- Stays contribute no new points to the geometric trace. Only genuine old
edges and the initial vertex are needed as supports. -/
lemma edgeTrace_edge_or_start
    (Q : Set (ClipSpace d)) (w : ℕ → ClipSpace d) (L : ℕ)
    (hsteps : ∀ k < L, w k = w (k + 1) ∨ Adj Q (w k) (w (k + 1)))
    {x : ClipSpace d} (hx : x ∈ edgeTrace w L) :
    x = w 0 ∨ ∃ k < L, Adj Q (w k) (w (k + 1)) ∧ x ∈ segment ℝ (w k) (w (k + 1)) := by
  induction L with
  | zero => exact Or.inl hx
  | succ L ih =>
    have hp : ∀ k < L, w k = w (k + 1) ∨ Adj Q (w k) (w (k + 1)) :=
      fun k hk => hsteps k (by omega)
    rcases hx with hx | hx
    · rcases ih hp hx with h | ⟨k, hk, hE, hx⟩
      · exact Or.inl h
      · exact Or.inr ⟨k, by omega, hE, hx⟩
    · rcases hsteps L (by omega) with he | hE
      · have hx' : x = w L := by simpa [← he] using hx
        have hxT : x ∈ edgeTrace w L := hx'.symm ▸ edgeTrace_end w L
        rcases ih hp hxT with h | ⟨k, hk, hE, hx⟩
        · exact Or.inl h
        · exact Or.inr ⟨k, by omega, hE, hx⟩
      · exact Or.inr ⟨L, by omega, hE, hx⟩

#print axioms extreme_outer_of_strict_cuts
#print axioms extreme_outer_or_on_final_cut
#print axioms outer_vertex_above
#print axioms outward_segment_retract_on_cut
#print axioms final_vertex_attachment
#print axioms edgeTrace_edge_or_start

end HirschRadial
