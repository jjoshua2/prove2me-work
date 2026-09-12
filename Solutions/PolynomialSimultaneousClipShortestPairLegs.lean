import Mathlib
import Solutions.PolynomialSimultaneousClipPairLegs
import Solutions.PolynomialShortestRegionRouting

/-!
# Simultaneous clipping with the actual shortest mixed repair path

The existing pair-specific clipping theorem returns the actual local cut legs,
but forgets the mixed region path from which they were assembled.  The new
carrier-excess tradeoff needs that same path to be shortest/chordless *before*
pair-specific costs are attached.

This module reuses the identical radial cover geometry, chooses a metric-shortest
path in its parent-vertex intersection graph, and only then builds the local
`RegionLeg`s.  The result retains both the shortest/chordless mixed path and the
actual cut portal pairs.  This is the interface needed to apply the verified
`localExcess + (r-3) <= n-d` theorem to the repair that is actually routed.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRegionRoute

set_option autoImplicit false
set_option maxHeartbeats 9000000

noncomputable section
namespace HirschRadial

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- The mixed final-parent repair regions attached to one concrete outer route.
Cut labels are final cut faces; old labels are clipped pieces of successive
outer edges; endpoint labels are the two singleton endpoints. -/
def clipRepairPathRegion {D : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (u v : EuclideanSpace ℝ (Fin d)) :
    Sum ι (Sum (Fin D) (Fin 2)) → Set (EuclideanSpace ℝ (Fin d))
  | .inl i => P ∩ {z | ⟪a i, z⟫ = b i}
  | .inr (.inl k) => P ∩ segment ℝ (w k.val) (w (k.val + 1))
  | .inr (.inr k) => {if k = 0 then u else v}

/-- Pair-specific simultaneous clipping on a supplied outer route while
retaining the same metric-shortest/chordless mixed region path used to construct
the local calls. -/
theorem route_clip_of_lifted_endpoints_with_shortest_pair_specific_cut_legs
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQc : IsCompact Q) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (D : ℕ)
    (B : ι → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℕ)
    (hFaces : ∀ i, ∀ p ∈ extremePoints ℝ (clipSet Q a b),
      ⟪a i, p⟫ = b i → ∀ q ∈ extremePoints ℝ (clipSet Q a b),
      ⟪a i, q⟫ = b i → Route (Adj (clipSet Q a b)) (B i p q) p q)
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
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
      ∃ i j : Sum ι (Sum (Fin D) (Fin 2)),
      ∃ p :
          (intersectionGraph (fun k =>
            extremePoints ℝ (clipSet Q a b) ∩
              clipRepairPathRegion (D := D) (clipSet Q a b) a b w u v k)).Walk i j,
        p.length =
          (intersectionGraph (fun k =>
            extremePoints ℝ (clipSet Q a b) ∩
              clipRepairPathRegion (D := D) (clipSet Q a b) a b w u v k)).dist i j ∧
        p.IsPath ∧ WalkChordless p ∧
        ∃ legs : List
            (RegionLeg (Sum ι (Sum (Fin D) (Fin 2)))
              (EuclideanSpace ℝ (Fin d))),
          legs.map RegionLeg.label = p.support ∧
          (legs.map RegionLeg.label).Nodup ∧
          (∀ cut ∈ clipRepairCutLegs legs,
            cut.entry ∈ extremePoints ℝ (clipSet Q a b) ∧
            ⟪a cut.label, cut.entry⟫ = b cut.label ∧
            cut.exit ∈ extremePoints ℝ (clipSet Q a b) ∧
            ⟪a cut.label, cut.exit⟫ = b cut.label) ∧
          Route (Adj (clipSet Q a b))
            (D + ((clipRepairCutLegs legs).map fun leg =>
              B leg.label leg.entry leg.exit).sum) u v := by
  classical
  let P := clipSet Q a b
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
  let F := clipRepairPathRegion (D := D) P a b w u v
  let C := clipRepairPairCost (D := D) B
  have hPc : IsCompact P := clipSet_compact Q hQc a b
  have hPv : Convex ℝ P := clipSet_convex Q hQ a b
  have hF : ∀ k, IsExtreme ℝ P (F k) := by
    intro k
    rcases k with i | (e | t)
    · exact HirschClipLift.supporting_equality_extreme P (a i) (b i)
        (fun z hz => hz.2 i)
    · exact HirschSubsegment.extreme_inter_of_parent_subset Q P _
        inter_subset_left (hOld e)
    · by_cases ht : t = 0
      · simpa [F, clipRepairPathRegion, ht] using (isExtreme_singleton.mpr hu)
      · simpa [F, clipRepairPathRegion, ht] using (isExtreme_singleton.mpr hv)
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
  have hlocal : ∀ k,
      ∀ p ∈ extremePoints ℝ P ∩ F k,
      ∀ q ∈ extremePoints ℝ P ∩ F k,
        Route (Adj P) (C k p q) p q := by
    intro k
    rcases k with i | (e | t)
    · intro p hp q hq
      change Route (Adj P) (B i p q) p q
      exact hFaces i p hp.1 hp.2.2 q hq.1 hq.2.2
    · intro p hp q hq
      change Route (Adj P) 1 p q
      exact extreme_face_region P (F (.inr (.inl e))) 1 (hF (.inr (.inl e)))
        (HirschSubsegment.diamLE_of_convex_subsegment _
          (hPv.inter (convex_segment _ _)) _ _ inter_subset_right) p hp q hq
    · intro p hp q hq
      change Route (Adj P) 0 p q
      exact extreme_face_region P (F (.inr (.inr t))) 0 (hF (.inr (.inr t)))
        (singleton_diamLE_zero _) p hp q hq
  let ρ := retract a b o
  have hρP : ∀ z ∈ Q, ρ z ∈ P :=
    fun z hz => retract_mem Q hQ a b o z ho hz hstrict
  have hρfix : ∀ z ∈ P, ρ z = z :=
    fun z hz => retract_fixes a b o z hstrict hz.2
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
        have h := congrArg
          (fun z : EuclideanSpace ℝ (Fin d) => ⟪a i, z⟫) heval
        simp only [inner_add_right, inner_smul_right] at h
        have htotal : α * b i + β * b i = b i := by
          rw [← add_mul, hsum, one_mul]
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
  obtain ⟨ri, rj, _hui, _hvj, p, hpdist, hpath, hchord,
      legs, hlabels, hnd, hfits, hr⟩ :=
    route_of_preconnected_face_cover_with_shortest_pair_specific_legs
      P F C hPc hF hFc hlocal (ρ '' K) himage hcover u v hu hv huK hvK
  have hcutValid : ∀ cut ∈ clipRepairCutLegs legs,
      cut.entry ∈ extremePoints ℝ P ∧
      ⟪a cut.label, cut.entry⟫ = b cut.label ∧
      cut.exit ∈ extremePoints ℝ P ∧
      ⟪a cut.label, cut.exit⟫ = b cut.label := by
    intro cut hcut
    change cut ∈ List.filterMap (fun leg =>
      match leg.label with
      | .inl i => some ⟨i, leg.entry, leg.exit⟩
      | .inr _ => none) legs at hcut
    rw [List.mem_filterMap] at hcut
    obtain ⟨mixed, hmixed, hmap⟩ := hcut
    rcases mixed with ⟨label, entry, exit⟩
    rcases label with i | rest
    · simp only at hmap
      injection hmap
      subst cut
      have hf := hfits (RegionLeg.mk (Sum.inl i) entry exit) hmixed
      have hentry : entry ∈ extremePoints ℝ P ∩ F (.inl i) := hf.1
      have hexit : exit ∈ extremePoints ℝ P ∩ F (.inl i) := hf.2.1
      exact ⟨hentry.1, hentry.2.2, hexit.1, hexit.2.2⟩
    · simp at hmap
  have hold : (clipRepairOldEdgeLabels (legs.map RegionLeg.label)).length ≤ D :=
    clipRepairOldEdgeLabels_length_le hnd
  have hcost := clipRepairPairCost_sum_eq_cut_add_old_length B legs
  have hle :
      (legs.map fun leg => C leg.label leg.entry leg.exit).sum ≤
        D + ((clipRepairCutLegs legs).map fun leg =>
          B leg.label leg.entry leg.exit).sum := by
    dsimp [C]
    rw [hcost]
    omega
  obtain ⟨route, hroute0, hrouteB, hrouteStep⟩ := hr
  have hfinalRoute : Route (Adj P)
      (D + ((clipRepairCutLegs legs).map fun leg =>
        B leg.label leg.entry leg.exit).sum) u v :=
    HirschProduct.pad_walk (Adj P) hle route hroute0 hrouteB hrouteStep
  refine ⟨w, ri, rj, ?_, ?_, ?_, ?_, legs, ?_, hnd, ?_, ?_⟩
  · simpa [P, F] using p
  · simpa [P, F] using hpdist
  · exact hpath
  · simpa [P, F] using hchord
  · exact hlabels
  · simpa [P] using hcutValid
  · simpa [P] using hfinalRoute

/-- Endpoint-lifted wrapper using any supplied outer diameter bound, retaining
the shortest/chordless mixed repair path and actual cut portal pairs. -/
theorem route_clip_with_shortest_pair_specific_cut_legs
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQc : IsCompact Q) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (D : ℕ)
    (B : ι → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℕ)
    (hD : DiamLE Q D)
    (hFaces : ∀ i, ∀ p ∈ extremePoints ℝ (clipSet Q a b),
      ⟪a i, p⟫ = b i → ∀ q ∈ extremePoints ℝ (clipSet Q a b),
      ⟪a i, q⟫ = b i → Route (Adj (clipSet Q a b)) (B i p q) p q)
    (o : EuclideanSpace ℝ (Fin d)) (ho : o ∈ Q)
    (hstrict : ∀ i, ⟪a i, o⟫ < b i)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (clipSet Q a b))
    (hv : v ∈ extremePoints ℝ (clipSet Q a b)) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
      ∃ i j : Sum ι (Sum (Fin D) (Fin 2)),
      ∃ p :
          (intersectionGraph (fun k =>
            extremePoints ℝ (clipSet Q a b) ∩
              clipRepairPathRegion (D := D) (clipSet Q a b) a b w u v k)).Walk i j,
        p.length =
          (intersectionGraph (fun k =>
            extremePoints ℝ (clipSet Q a b) ∩
              clipRepairPathRegion (D := D) (clipSet Q a b) a b w u v k)).dist i j ∧
        p.IsPath ∧ WalkChordless p ∧
        ∃ legs : List
            (RegionLeg (Sum ι (Sum (Fin D) (Fin 2)))
              (EuclideanSpace ℝ (Fin d))),
          legs.map RegionLeg.label = p.support ∧
          (legs.map RegionLeg.label).Nodup ∧
          (∀ cut ∈ clipRepairCutLegs legs,
            cut.entry ∈ extremePoints ℝ (clipSet Q a b) ∧
            ⟪a cut.label, cut.entry⟫ = b cut.label ∧
            cut.exit ∈ extremePoints ℝ (clipSet Q a b) ∧
            ⟪a cut.label, cut.exit⟫ = b cut.label) ∧
          Route (Adj (clipSet Q a b))
            (D + ((clipRepairCutLegs legs).map fun leg =>
              B leg.label leg.entry leg.exit).sum) u v := by
  obtain ⟨x, hx, hux⟩ :=
    HirschClipLift.endpoint_lift_to_outer_vertex Q hQc hQ a b u hu
  obtain ⟨y, hy, hvy⟩ :=
    HirschClipLift.endpoint_lift_to_outer_vertex Q hQc hQ a b v hv
  exact route_clip_of_lifted_endpoints_with_shortest_pair_specific_cut_legs
    Q hQc hQ a b D B hFaces o ho hstrict u v hu hv
    x y hx hy hux hvy (hD x hx y hy)

#print axioms clipRepairPathRegion
#print axioms route_clip_of_lifted_endpoints_with_shortest_pair_specific_cut_legs
#print axioms route_clip_with_shortest_pair_specific_cut_legs

end HirschRadial
