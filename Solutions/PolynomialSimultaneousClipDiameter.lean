import Solutions.PolynomialClosedFaceTrace
import Solutions.PolynomialConvexSubsegment
import Solutions.PolynomialClipEndpointLift
import Solutions.PolynomialAdjEndpoints

/-! Simultaneous clipping with FINAL face budgets and newly created endpoints.
Verification status is recorded in research/ClippingVerificationProgress.md. -/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRadial

variable {d : ℕ} {ι : Type*} [Fintype ι]

lemma clipSet_convex (Q : Set (EuclideanSpace ℝ (Fin d))) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ) : Convex ℝ (clipSet Q a b) := by
  intro x hx y hy α β hα hβ hsum
  refine ⟨hQ hx.1 hy.1 hα hβ hsum, ?_⟩
  intro i
  simp only [inner_add_right, inner_smul_right]
  have htotal : α * b i + β * b i = b i := by rw [← add_mul, hsum, one_mul]
  linarith [mul_le_mul_of_nonneg_left (hx.2 i) hα,
    mul_le_mul_of_nonneg_left (hy.2 i) hβ]

lemma clipSet_compact (Q : Set (EuclideanSpace ℝ (Fin d))) (hQ : IsCompact Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ) : IsCompact (clipSet Q a b) := by
  have hclosed : IsClosed {x : EuclideanSpace ℝ (Fin d) | ∀ i, ⟪a i, x⟫ ≤ b i} := by
    have heq : {x : EuclideanSpace ℝ (Fin d) | ∀ i, ⟪a i, x⟫ ≤ b i} =
        ⋂ i, {x | ⟪a i, x⟫ ≤ b i} := by ext x; simp
    rw [heq]
    exact isClosed_iInter (fun i => isClosed_le (by fun_prop) continuous_const)
  exact hQ.inter_right hclosed

def walkTrace (w : ℕ → EuclideanSpace ℝ (Fin d)) : ℕ → Set (EuclideanSpace ℝ (Fin d))
  | 0 => {w 0}
  | n + 1 => walkTrace w n ∪ segment ℝ (w n) (w (n + 1))

lemma walkTrace_start (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ) : w 0 ∈ walkTrace w L := by
  induction L with
  | zero => exact mem_singleton _
  | succ L ih => exact Or.inl ih

lemma walkTrace_end (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ) : w L ∈ walkTrace w L := by
  cases L with
  | zero => exact mem_singleton _
  | succ L => exact Or.inr (right_mem_segment ℝ _ _)

lemma walkTrace_preconnected (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ) :
    IsPreconnected (walkTrace w L) := by
  induction L with
  | zero => exact isPreconnected_singleton
  | succ L ih =>
      exact ih.union (w L) (walkTrace_end w L) (left_mem_segment ℝ _ _)
        (convex_segment (w L) (w (L + 1))).isPreconnected

lemma singleton_diamLE_zero (u : EuclideanSpace ℝ (Fin d)) : DiamLE ({u} : Set _) 0 := by
  intro x hx y hy
  have hx' : x = u := by simpa using hx
  have hy' : y = u := by simpa using hy
  subst x
  subst y
  exact ⟨fun _ => u, rfl, rfl, fun _ h => False.elim (Nat.not_lt_zero _ h)⟩

/-- The endpoint spokes and the middle route charge the same final face family
only once. Only compactness and the explicit outer/face budgets are assumed. -/
theorem diamLE_clip_of_strict_centre
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQc : IsCompact Q) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (D : ℕ) (B : ι → ℕ) (hD : DiamLE Q D)
    (hFaces : ∀ i, DiamLE (clipSet Q a b ∩ {z | ⟪a i, z⟫ = b i}) (B i))
    (o : EuclideanSpace ℝ (Fin d)) (ho : o ∈ Q) (hstrict : ∀ i, ⟪a i, o⟫ < b i) :
    DiamLE (clipSet Q a b) (D + ∑ i, B i) := by
  classical
  let P := clipSet Q a b
  have hPc : IsCompact P := clipSet_compact Q hQc a b
  have hPv : Convex ℝ P := clipSet_convex Q hQ a b
  intro u hu v hv
  obtain ⟨x, hx, hux⟩ := HirschClipLift.endpoint_lift_to_outer_vertex Q hQc hQ a b u hu
  obtain ⟨y, hy, hvy⟩ := HirschClipLift.endpoint_lift_to_outer_vertex Q hQc hQ a b v hv
  obtain ⟨w, hw0, hwD, hstep⟩ := hD x hx y hy
  have hwv : ∀ k ≤ D, w k ∈ extremePoints ℝ Q := by
    intro k
    induction k with
    | zero => intro _; simpa [hw0] using hx
    | succ k ih =>
        intro hk
        rcases hstep k (by omega) with heq | hedge
        · rw [← heq]
          exact ih (by omega)
        · exact HirschPolynomialAccess.adj_right_extreme Q hedge
  have hOld : ∀ k : Fin D, IsExtreme ℝ Q (segment ℝ (w k.val) (w (k.val + 1))) := by
    intro k
    rcases hstep k.val k.isLt with heq | hedge
    · rw [heq, segment_same]
      exact isExtreme_singleton.mpr (hwv (k.val + 1) (by omega))
    · exact hedge.2
  let F : Sum ι (Sum (Fin D) (Fin 2)) → Set (EuclideanSpace ℝ (Fin d))
    | .inl i => P ∩ {z | ⟪a i, z⟫ = b i}
    | .inr (.inl k) => P ∩ segment ℝ (w k.val) (w (k.val + 1))
    | .inr (.inr k) => {if k = 0 then u else v}
  let C : Sum ι (Sum (Fin D) (Fin 2)) → ℕ
    | .inl i => B i
    | .inr (.inl _) => 1
    | .inr (.inr _) => 0
  have hF : ∀ k, IsExtreme ℝ P (F k) := by
    intro k
    rcases k with i | (e | t)
    · exact HirschClipLift.supporting_equality_extreme P (a i) (b i)
        (fun z hz => hz.2 i)
    · exact HirschSubsegment.extreme_inter_of_parent_subset Q P _
        inter_subset_left (hOld e)
    · by_cases ht : t = 0
      · simpa [F, ht] using (isExtreme_singleton.mpr hu)
      · simpa [F, ht] using (isExtreme_singleton.mpr hv)
  have hFc : ∀ k, IsClosed (F k) := by
    intro k
    rcases k with i | (e | t)
    · exact hPc.isClosed.inter (isClosed_eq (by fun_prop) continuous_const)
    · apply hPc.isClosed.inter
      have hc : IsCompact (segment ℝ (w e.val) (w (e.val + 1))) := by
        rw [segment_eq_image]
        exact isCompact_Icc.image (by fun_prop)
      exact hc.isClosed
    · exact isClosed_singleton
  have hFD : ∀ k, DiamLE (F k) (C k) := by
    intro k
    rcases k with i | (e | t)
    · exact hFaces i
    · exact HirschSubsegment.diamLE_of_convex_subsegment _
        (hPv.inter (convex_segment _ _)) _ _ inter_subset_right
    · exact singleton_diamLE_zero _
  let ρ := retract a b o
  have hρP : ∀ z ∈ Q, ρ z ∈ P := fun z hz => retract_mem Q hQ a b o z ho hz hstrict
  have hρfix : ∀ z ∈ P, ρ z = z := fun z hz => retract_fixes a b o z hstrict hz.2
  have hspoke : ∀ (e z : EuclideanSpace ℝ (Fin d)), e ∈ P → z ∈ Q →
      (e = z ∨ ∃ i, ⟪a i, e⟫ = b i ∧ b i ≤ ⟪a i, z⟫) →
      (∃ k : Fin 2, e = if k = 0 then u else v) →
      ∀ t ∈ segment ℝ e z, ∃ k, ρ t ∈ F k := by
    intro e z he hz hez hend t ht
    rcases hez with heq | ⟨i, hei, hzi⟩
    · have hte : t = e := by simpa [← heq] using ht
      obtain ⟨k, hk⟩ := hend
      refine ⟨.inr (.inr k), ?_⟩
      change ρ t = if k = 0 then u else v
      exact (congrArg ρ hte).trans ((hρfix e he).trans hk)
    · have htQ : t ∈ Q := hQ.segment_subset he.1 hz ht
      have hit : b i ≤ ⟪a i, t⟫ := by
        obtain ⟨α, β, hα, hβ, hsum, heval⟩ := ht
        have h := congrArg (fun z : EuclideanSpace ℝ (Fin d) => ⟪a i, z⟫) heval
        simp only [inner_add_right, inner_smul_right] at h
        have htotal : α * b i + β * b i = b i := by rw [← add_mul, hsum, one_mul]
        rw [hei] at h
        linarith [mul_le_mul_of_nonneg_left hzi hβ]
      obtain ⟨j, hj⟩ := retract_on_cut_of_exceeded a b o t hstrict i hit
      exact ⟨.inl j, hρP t htQ, hj⟩
  have hleft : ∀ t ∈ segment ℝ u x, ∃ k, ρ t ∈ F k :=
    hspoke u x hu.1 hx.1 hux ⟨0, by simp⟩
  have hright : ∀ t ∈ segment ℝ v y, ∃ k, ρ t ∈ F k :=
    hspoke v y hv.1 hy.1 hvy ⟨1, by simp⟩
  have htrace : ∀ L ≤ D, ∀ z ∈ walkTrace w L, ∃ k, ρ z ∈ F k := by
    intro L
    induction L with
    | zero =>
        intro _ z hz
        have hz0 : z = w 0 := hz
        subst z
        rw [hw0]
        exact hleft x (right_mem_segment ℝ _ _)
    | succ L ih =>
        intro hL z hz
        rcases hz with hz | hz
        · exact ih (by omega) z hz
        · have hzQ : z ∈ Q := hQ.segment_subset (hwv L (by omega)).1
            (hwv (L + 1) (by omega)).1 hz
          rcases retract_eq_self_or_on_cut a b o z hstrict with hfix | ⟨i, hi⟩
          · refine ⟨.inr (.inl ⟨L, by omega⟩), hρP z hzQ, ?_⟩
            simpa [ρ, hfix] using hz
          · exact ⟨.inl i, hρP z hzQ, hi⟩
  let K := (segment ℝ u x ∪ walkTrace w D) ∪ segment ℝ v y
  have hK : IsPreconnected K := by
    have h1 : IsPreconnected (segment ℝ u x ∪ walkTrace w D) :=
      (convex_segment u x).isPreconnected.union x (right_mem_segment ℝ _ _)
        (by simpa [hw0] using walkTrace_start w D) (walkTrace_preconnected w D)
    exact h1.union y (Or.inr (by simpa [hwD] using walkTrace_end w D))
      (right_mem_segment ℝ _ _) (convex_segment v y).isPreconnected
  have himage : IsPreconnected (ρ '' K) :=
    hK.image ρ (continuous_retract a b o).continuousOn
  have hcover : ∀ z ∈ ρ '' K, ∃ k, z ∈ F k := by
    rintro _ ⟨z, hz, rfl⟩
    rcases hz with (hz | hz) | hz
    · exact hleft z hz
    · exact htrace D (le_refl _) z hz
    · exact hright z hz
  have huK : u ∈ ρ '' K :=
    ⟨u, Or.inl (Or.inl (left_mem_segment ℝ _ _)), hρfix u hu.1⟩
  have hvK : v ∈ ρ '' K :=
    ⟨v, Or.inr (left_mem_segment ℝ _ _), hρfix v hv.1⟩
  have hr := HirschRegionRoute.route_of_preconnected_face_cover P F C hPc hF hFc hFD
    (ρ '' K) himage hcover u v hu hv huK hvK
  simpa [C, Fintype.sum_sum_type, Nat.add_comm] using hr

lemma strict_centre_or_universal_cut
    (P : Set (EuclideanSpace ℝ (Fin d))) (hP : Convex ℝ P) (hne : P.Nonempty)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (hbound : ∀ i, ∀ x ∈ P, ⟪a i, x⟫ ≤ b i) :
    (∃ o ∈ P, ∀ i, ⟪a i, o⟫ < b i) ∨ (∃ i, ∀ x ∈ P, ⟪a i, x⟫ = b i) := by
  classical
  by_cases huniv : ∃ i, ∀ x ∈ P, ⟪a i, x⟫ = b i
  · exact Or.inr huniv
  have hpoint : ∀ i, ∃ x ∈ P, ⟪a i, x⟫ < b i := by
    intro i
    by_contra h
    push_neg at h
    apply huniv
    exact ⟨i, fun x hx => le_antisymm (hbound i x hx) (h x hx)⟩
  have hfinite : ∀ s : Finset ι, ∃ o ∈ P, ∀ i ∈ s, ⟪a i, o⟫ < b i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        obtain ⟨o, ho⟩ := hne
        exact ⟨o, ho, by simp⟩
    | @insert i s hi ih =>
        obtain ⟨o, ho, hs⟩ := ih
        obtain ⟨x, hx, hix⟩ := hpoint i
        refine ⟨(1 / 2 : ℝ) • o + (1 / 2 : ℝ) • x,
          hP ho hx (by norm_num) (by norm_num) (by norm_num), ?_⟩
        intro j hj
        simp only [inner_add_right, inner_smul_right]
        rcases Finset.mem_insert.mp hj with rfl | hj
        · nlinarith [hbound j o ho]
        · nlinarith [hs j hj, hbound j x hx]
  obtain ⟨o, ho, hs⟩ := hfinite Finset.univ
  exact Or.inl ⟨o, ho, fun i => hs i (Finset.mem_univ _)⟩

/-- All-vertex diameter transfer under simultaneous clipping by finitely many
halfspaces. Face budgets refer to the FINAL intersection, not intermediate sets. -/
theorem simultaneous_clipping_diameter_bound
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQc : IsCompact Q) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (D : ℕ) (B : ι → ℕ) (hD : DiamLE Q D)
    (hFaces : ∀ i, DiamLE (clipSet Q a b ∩ {z | ⟪a i, z⟫ = b i}) (B i)) :
    DiamLE (clipSet Q a b) (D + ∑ i, B i) := by
  classical
  let P := clipSet Q a b
  by_cases hne : P.Nonempty
  · rcases strict_centre_or_universal_cut P (clipSet_convex Q hQ a b) hne a b
        (fun i x hx => hx.2 i) with ⟨o, ho, hs⟩ | ⟨i, hi⟩
    · exact diamLE_clip_of_strict_centre Q hQc hQ a b D B hD hFaces o ho.1 hs
    · have heq : P ∩ {z | ⟪a i, z⟫ = b i} = P := by
        apply inter_eq_left.mpr
        exact fun z hz => hi z hz
      have hPi : DiamLE P (B i) := by
        have h := hFaces i
        change DiamLE (P ∩ {z | ⟪a i, z⟫ = b i}) (B i) at h
        rw [heq] at h
        exact h
      have hle : B i ≤ D + ∑ j, B j := by
        have hsum : B i ≤ ∑ j, B j :=
          Finset.single_le_sum (fun j _ => Nat.zero_le (B j)) (Finset.mem_univ i)
        omega
      intro u hu v hv
      obtain ⟨w, hw0, hwB, hwstep⟩ := hPi u hu v hv
      exact HirschProduct.pad_walk (Adj P) hle w hw0 hwB hwstep
  · intro u hu v hv
    exact False.elim (hne ⟨u, hu.1⟩)

#print axioms clipSet_convex
#print axioms clipSet_compact
#print axioms walkTrace_start
#print axioms walkTrace_end
#print axioms walkTrace_preconnected
#print axioms singleton_diamLE_zero
#print axioms diamLE_clip_of_strict_centre
#print axioms strict_centre_or_universal_cut
#print axioms simultaneous_clipping_diameter_bound

end HirschRadial
