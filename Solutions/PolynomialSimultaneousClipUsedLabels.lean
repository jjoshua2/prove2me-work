import Solutions.PolynomialSimultaneousClipParentRoutes
import Solutions.PolynomialUsedRegionRouting

/-!
Path-sensitive simultaneous clipping.

The existing repair theorem charges every available cut-face budget, every old
walk edge, and the two endpoint singleton regions via one padded global sum.
This module exposes the ACTUAL simple region-label path selected by the
intersection-graph routing theorem.  The returned list is `Nodup`, and its
route length is exactly the sum of the costs of those labels.

A subsequent corollary can project the `.inl` labels to the actual cut faces
and bound the distinct old-edge labels by `D`.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRegionRoute

set_option autoImplicit false
set_option maxHeartbeats 6000000

noncomputable section
namespace HirschRadial

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- Cost attached to the three kinds of repair regions used by the radial
simultaneous-clipping construction. -/
def clipUsedRegionCost {D : ℕ} (B : ι → ℕ) :
    Sum ι (Sum (Fin D) (Fin 2)) → ℕ
  | .inl i => B i
  | .inr (.inl _) => 1
  | .inr (.inr _) => 0

/-- Path-sensitive form of
`route_clip_of_lifted_endpoints_with_parent_routes`.

Instead of immediately padding to `D + sum_i B_i`, return the exact simple
region-label support selected by the connected-face routing proof.  The labels
are pairwise distinct and the route cost is exactly the sum of their local
costs. -/
theorem route_clip_of_lifted_endpoints_with_parent_routes_used_labels
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQc : IsCompact Q) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (D : ℕ) (B : ι → ℕ)
    (hFaces : ∀ i, ∀ p ∈ extremePoints ℝ (clipSet Q a b),
      ⟪a i, p⟫ = b i → ∀ q ∈ extremePoints ℝ (clipSet Q a b),
      ⟪a i, q⟫ = b i → Route (Adj (clipSet Q a b)) (B i) p q)
    (o : EuclideanSpace ℝ (Fin d)) (ho : o ∈ Q)
    (hstrict : ∀ i, ⟪a i, o⟫ < b i)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (clipSet Q a b))
    (hv : v ∈ extremePoints ℝ (clipSet Q a b))
    (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ Q) (hy : y ∈ extremePoints ℝ Q)
    (hux : u = x ∨ ∃ i, ⟪a i, u⟫ = b i ∧ b i ≤ ⟪a i, x⟫)
    (hvy : v = y ∨ ∃ i, ⟪a i, v⟫ = b i ∧ b i ≤ ⟪a i, y⟫)
    (hwalk : Route (Adj Q) D x y) :
    ∃ l : List (Sum ι (Sum (Fin D) (Fin 2))),
      l.Nodup ∧
      Route (Adj (clipSet Q a b)) ((l.map (clipUsedRegionCost B)).sum) u v := by
  classical
  let P := clipSet Q a b
  have hPc : IsCompact P := clipSet_compact Q hQc a b
  have hPv : Convex ℝ P := clipSet_convex Q hQ a b
  obtain ⟨w, hw0, hwD, hstep⟩ := hwalk
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
  have hlocal : ∀ k, ∀ p ∈ extremePoints ℝ P ∩ F k,
      ∀ q ∈ extremePoints ℝ P ∩ F k,
        Route (Adj P) (clipUsedRegionCost B k) p q := by
    intro k
    rcases k with i | (e | t)
    · intro p hp q hq
      exact hFaces i p hp.1 hp.2.2 q hq.1 hq.2.2
    · simpa [clipUsedRegionCost] using
        (extreme_face_region P (F (.inr (.inl e))) 1 (hF (.inr (.inl e)))
          (HirschSubsegment.diamLE_of_convex_subsegment _
            (hPv.inter (convex_segment _ _)) _ _ inter_subset_right))
    · simpa [clipUsedRegionCost] using
        (extreme_face_region P (F (.inr (.inr t))) 0 (hF (.inr (.inr t)))
          (singleton_diamLE_zero _))
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
  exact route_of_preconnected_face_cover_with_parent_routes_used_labels
    P F (clipUsedRegionCost B) hPc hF hFc hlocal
    (ρ '' K) himage hcover u v hu hv huK hvK

#print axioms clipUsedRegionCost
#print axioms route_clip_of_lifted_endpoints_with_parent_routes_used_labels

end HirschRadial
