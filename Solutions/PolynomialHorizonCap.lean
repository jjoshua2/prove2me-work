import Solutions.PolynomialSimultaneousClipDiameter

/-! Helper lemmas for the pointed-unbounded extension.
The general cap-existence and three-case assembly are not proved in this file. -/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschHorizon

variable {d : ℕ} {ι : Type*} [Fintype ι]

def cap (Q : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (T : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  Q ∩ {x | ⟪c, x⟫ ≤ T}

lemma clip_cap_eq
    (Q : Set (EuclideanSpace ℝ (Fin d)))
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (T : ℝ)
    (hbound : ∀ x ∈ HirschRadial.clipSet Q a b, ⟪c, x⟫ ≤ T) :
    HirschRadial.clipSet (cap Q c T) a b = HirschRadial.clipSet Q a b := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1.1, hx.2⟩
  · intro hx
    exact ⟨⟨hx.1, hbound x hx⟩, hx.2⟩

lemma cap_vertex_old_or_horizon
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQ : Convex ℝ Q)
    (c : EuclideanSpace ℝ (Fin d)) (T : ℝ)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ extremePoints ℝ (cap Q c T)) :
    x ∈ extremePoints ℝ Q ∨ ⟪c, x⟫ = T := by
  have hcap := hx.1.2
  change ⟪c, x⟫ ≤ T at hcap
  rcases hcap.eq_or_lt with heq | hlt
  · exact Or.inr heq
  · exact Or.inl (HirschCut.strict_cut_extreme_to_parent Q hQ c T hx hlt)

lemma exterior_retract_on_cut
    (Q : Set (EuclideanSpace ℝ (Fin d)))
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (o x : EuclideanSpace ℝ (Fin d))
    (hstrict : ∀ i, ⟪a i, o⟫ < b i)
    (hx : x ∈ Q) (hout : x ∉ HirschRadial.clipSet Q a b) :
    ∃ i, ⟪a i, HirschRadial.retract a b o x⟫ = b i := by
  classical
  have hnot : ¬ ∀ i, ⟪a i, x⟫ ≤ b i := fun h => hout ⟨hx, h⟩
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  exact HirschRadial.retract_on_cut_of_exceeded a b o x hstrict i
    (lt_of_not_ge hi).le

lemma horizon_retract_final_face
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (o : EuclideanSpace ℝ (Fin d)) (ho : o ∈ Q)
    (hstrict : ∀ i, ⟪a i, o⟫ < b i)
    (c : EuclideanSpace ℝ (Fin d)) (T : ℝ)
    (hsep : ∀ z ∈ HirschRadial.clipSet Q a b, ⟪c, z⟫ < T)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Q) (hheight : T ≤ ⟪c, x⟫) :
    ∃ i, HirschRadial.retract a b o x ∈
      HirschRadial.clipSet Q a b ∩ {z | ⟪a i, z⟫ = b i} := by
  have hout : x ∉ HirschRadial.clipSet Q a b := fun h =>
    (not_lt_of_ge hheight) (hsep x h)
  obtain ⟨i, hi⟩ := exterior_retract_on_cut Q a b o x hstrict hx hout
  exact ⟨i, HirschRadial.retract_mem Q hQ a b o x ho hx hstrict, hi⟩

lemma horizon_chord_shadow
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (o : EuclideanSpace ℝ (Fin d)) (ho : o ∈ Q)
    (hstrict : ∀ i, ⟪a i, o⟫ < b i)
    (c : EuclideanSpace ℝ (Fin d)) (T : ℝ)
    (hsep : ∀ z ∈ HirschRadial.clipSet Q a b, ⟪c, z⟫ < T)
    (x y : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Q) (hy : y ∈ Q)
    (hxc : ⟪c, x⟫ = T) (hyc : ⟪c, y⟫ = T) :
    ∀ z ∈ segment ℝ x y, ∃ i, HirschRadial.retract a b o z ∈
      HirschRadial.clipSet Q a b ∩ {p | ⟪a i, p⟫ = b i} := by
  intro z hz
  have hzQ := hQ.segment_subset hx hy hz
  have hzc : ⟪c, z⟫ = T := by
    obtain ⟨α, β, _, _, hsum, rfl⟩ := hz
    simp only [inner_add_right, inner_smul_right, hxc, hyc]
    rw [← add_mul, hsum, one_mul]
  exact horizon_retract_final_face Q hQ a b o ho hstrict c T hsep z hzQ hzc.ge

lemma endpoint_lift_to_old_or_horizon
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (T : ℝ)
    (hcap : IsCompact (cap Q c T))
    (hcapconv : Convex ℝ (cap Q c T))
    (hbound : ∀ x ∈ HirschRadial.clipSet Q a b, ⟪c, x⟫ ≤ T)
    (u : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (HirschRadial.clipSet Q a b)) :
    ∃ x, x ∈ Q ∧ (x ∈ extremePoints ℝ Q ∨ ⟪c, x⟫ = T) ∧
      (u = x ∨ ∃ i, ⟪a i, u⟫ = b i ∧ b i ≤ ⟪a i, x⟫) := by
  have hu' : u ∈ extremePoints ℝ (HirschRadial.clipSet (cap Q c T) a b) := by
    rw [clip_cap_eq Q a b c T hbound]
    exact hu
  obtain ⟨x, hx, hux⟩ := HirschClipLift.endpoint_lift_to_outer_vertex
    (cap Q c T) hcap hcapconv a b u hu'
  exact ⟨x, hx.1.1, cap_vertex_old_or_horizon Q hQ c T hx, hux⟩

lemma clipped_cap_edge_budget
    (R P : Set (EuclideanSpace ℝ (Fin d))) (hPR : P ⊆ R)
    (hPc : IsCompact P) (hP : Convex ℝ P)
    (x y : EuclideanSpace ℝ (Fin d)) (hxy : Adj R x y) :
    IsExtreme ℝ P (P ∩ segment ℝ x y) ∧
    IsClosed (P ∩ segment ℝ x y) ∧ DiamLE (P ∩ segment ℝ x y) 1 := by
  have hc : IsCompact (segment ℝ x y) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  exact ⟨HirschSubsegment.extreme_inter_of_parent_subset R P _ hPR hxy.2,
    hPc.isClosed.inter hc.isClosed,
    HirschSubsegment.diamLE_of_convex_subsegment _
      (hP.inter (convex_segment x y)) x y inter_subset_right⟩

lemma first_horizon_edge
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQ : Convex ℝ Q)
    (c : EuclideanSpace ℝ (Fin d)) (T : ℝ)
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hverts : ∀ k ≤ L, w k ∈ extremePoints ℝ (cap Q c T))
    (hstep : ∀ k < L, w k = w (k + 1) ∨ Adj (cap Q c T) (w k) (w (k + 1)))
    (hstart : ⟪c, w 0⟫ < T) (hend : ⟪c, w L⟫ = T) :
    ∃ x y, x ∈ extremePoints ℝ Q ∧ y ∈ cap Q c T ∧
      ⟪c, y⟫ = T ∧ Adj (cap Q c T) x y := by
  classical
  have hex : ∃ k : ℕ, k ≤ L ∧ ⟪c, w k⟫ = T := ⟨L, le_refl _, hend⟩
  let m := Nat.find hex
  have hm : m ≤ L ∧ ⟪c, w m⟫ = T := Nat.find_spec hex
  have hmpos : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by omega
    exact hstart.ne (by simpa [hm0] using hm.2)
  have hmminus : m - 1 + 1 = m := by omega
  have hprev : ⟪c, w (m - 1)⟫ ≠ T := by
    intro h
    have hminimal := Nat.find_min hex (show m - 1 < m by omega)
    exact hminimal ⟨by omega, h⟩
  have hvprev := hverts (m - 1) (by omega)
  have hstrict : ⟪c, w (m - 1)⟫ < T := by
    have hle : ⟪c, w (m - 1)⟫ ≤ T := hvprev.1.2
    rcases hle.eq_or_lt with heq | hlt
    · exact False.elim (hprev heq)
    · exact hlt
  have hold := HirschCut.strict_cut_extreme_to_parent Q hQ c T hvprev hstrict
  have hedge : Adj (cap Q c T) (w (m - 1)) (w m) := by
    rcases hstep (m - 1) (by omega) with heq | he
    · have hsame : w (m - 1) = w m := by simpa [hmminus] using heq
      exact False.elim (hprev (by rw [hsame]; exact hm.2))
    · simpa [hmminus] using he
  exact ⟨w (m - 1), w m, hold, (hverts m hm.1).1, hm.2, hedge⟩

#print axioms clip_cap_eq
#print axioms cap_vertex_old_or_horizon
#print axioms exterior_retract_on_cut
#print axioms horizon_retract_final_face
#print axioms horizon_chord_shadow
#print axioms endpoint_lift_to_old_or_horizon
#print axioms clipped_cap_edge_budget
#print axioms first_horizon_edge

end HirschHorizon
