import Mathlib
import Solutions.PolynomialSimultaneousClipUsedRegions
import Solutions.PolynomialPairSpecificRegionLegs

/-!
# Pair-specific simultaneous clipping

This is the pair-specific refinement of simultaneous radial clipping.  The
repair still runs through the same mixed region cover (final cut faces, pieces
of the chosen outer route, and two endpoint singletons), but the local cost of
a final cut face may now depend on the actual parent-vertex entry/exit pair.

The returned mixed `RegionLeg` list has duplicate-free labels.  Projecting it to
cut legs retains the actual entry/exit vertices, which are certified parent
extreme vertices tight on the corresponding cut row.  The exact mixed cost
splits into pair-specific cut-leg costs plus one unit for each used old
outer-edge label; duplicate-freeness bounds the latter by the original outer
route budget `D`.  Hence the clean route budget is

`D + sum(pair-specific costs of the actual used cut legs)`.

No bound on those cut-leg costs is asserted here.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRegionRoute

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
namespace HirschRadial

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- Pair-specific local cost on the mixed clipping cover. -/
def clipRepairPairCost {D : ℕ}
    (B : ι → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℕ) :
    Sum ι (Sum (Fin D) (Fin 2)) →
      EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℕ
  | .inl i, p, q => B i p q
  | .inr (.inl _), _, _ => 1
  | .inr (.inr _), _, _ => 0

/-- Keep only cut-face legs, retaining their actual entry/exit vertices. -/
def clipRepairCutLegs {D : ℕ}
    (legs : List
      (RegionLeg (Sum ι (Sum (Fin D) (Fin 2))) (EuclideanSpace ℝ (Fin d)))) :
    List (RegionLeg ι (EuclideanSpace ℝ (Fin d))) :=
  legs.filterMap fun leg =>
    match leg.label with
    | .inl i => some ⟨i, leg.entry, leg.exit⟩
    | .inr _ => none

/-- The labels of projected cut legs are exactly the cut-label projection of
the mixed leg labels. -/
theorem clipRepairCutLeg_labels_eq {D : ℕ}
    (legs : List
      (RegionLeg (Sum ι (Sum (Fin D) (Fin 2))) (EuclideanSpace ℝ (Fin d)))) :
    (clipRepairCutLegs legs).map RegionLeg.label =
      clipRepairCutLabels (legs.map RegionLeg.label) := by
  induction legs with
  | nil => simp [clipRepairCutLegs, clipRepairCutLabels]
  | cons leg legs ih =>
      rcases leg with ⟨label, entry, exit⟩
      rcases label with i | rest
      · simp [clipRepairCutLegs, clipRepairCutLabels, ih]
      · simp [clipRepairCutLegs, clipRepairCutLabels, ih]

/-- Duplicate-free mixed labels imply duplicate-free cut-leg labels. -/
theorem clipRepairCutLeg_labels_nodup {D : ℕ}
    {legs : List
      (RegionLeg (Sum ι (Sum (Fin D) (Fin 2))) (EuclideanSpace ℝ (Fin d)))}
    (hnd : (legs.map RegionLeg.label).Nodup) :
    ((clipRepairCutLegs legs).map RegionLeg.label).Nodup := by
  rw [clipRepairCutLeg_labels_eq]
  exact clipRepairCutLabels_nodup hnd

/-- Exact mixed-leg cost decomposition: pair-specific cut-leg costs plus one
unit per used old outer-edge label. Endpoint singleton legs cost zero. -/
theorem clipRepairPairCost_sum_eq_cut_add_old_length {D : ℕ}
    (B : ι → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℕ)
    (legs : List
      (RegionLeg (Sum ι (Sum (Fin D) (Fin 2))) (EuclideanSpace ℝ (Fin d)))) :
    (legs.map fun leg =>
      clipRepairPairCost (D := D) B leg.label leg.entry leg.exit).sum =
      ((clipRepairCutLegs legs).map fun leg =>
        B leg.label leg.entry leg.exit).sum +
      (clipRepairOldEdgeLabels (legs.map RegionLeg.label)).length := by
  induction legs with
  | nil =>
      simp [clipRepairPairCost, clipRepairCutLegs, clipRepairOldEdgeLabels]
  | cons leg legs ih =>
      rcases leg with ⟨label, entry, exit⟩
      rcases label with i | rest
      · simp [clipRepairPairCost, clipRepairCutLegs, clipRepairOldEdgeLabels,
          ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · rcases rest with k | t
        · simp [clipRepairPairCost, clipRepairCutLegs, clipRepairOldEdgeLabels,
            ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        · simp [clipRepairPairCost, clipRepairCutLegs, clipRepairOldEdgeLabels, ih]

/-- Pair-specific simultaneous clipping on a supplied outer route.  Each
projected cut leg is an actual parent-vertex pair tight on that cut row.  After
absorbing at most `D` distinct old-edge legs, only the actual cut-leg pair costs
remain. -/
theorem route_clip_of_lifted_endpoints_with_pair_specific_cut_legs
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
    ∃ legs : List
        (RegionLeg (Sum ι (Sum (Fin D) (Fin 2))) (EuclideanSpace ℝ (Fin d))),
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
  let F : Sum ι (Sum (Fin D) (Fin 2)) → Set (EuclideanSpace ℝ (Fin d))
    | .inl i => P ∩ {z | ⟪a i, z⟫ = b i}
    | .inr (.inl k) => P ∩ segment ℝ (w k.val) (w (k.val + 1))
    | .inr (.inr k) => {if k = 0 then u else v}
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
  obtain ⟨_i, _j, _hui, _hvj, _p, _hp, legs, _hlabels, hnd, hfits, hr⟩ :=
    route_of_preconnected_face_cover_with_pair_specific_legs
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
      injection hmap with hEq
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
  refine ⟨legs, hnd, ?_, ?_⟩
  · simpa [P] using hcutValid
  · obtain ⟨q, hq0, hqB, hqs⟩ := hr
    exact HirschProduct.pad_walk (Adj P) hle q hq0 hqB hqs

/-- Pairwise endpoint-lifted wrapper. -/
theorem route_clip_with_pair_specific_cut_legs
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
    ∃ legs : List
        (RegionLeg (Sum ι (Sum (Fin D) (Fin 2))) (EuclideanSpace ℝ (Fin d))),
      (legs.map RegionLeg.label).Nodup ∧
      (∀ cut ∈ clipRepairCutLegs legs,
        cut.entry ∈ extremePoints ℝ (clipSet Q a b) ∧
        ⟪a cut.label, cut.entry⟫ = b cut.label ∧
        cut.exit ∈ extremePoints ℝ (clipSet Q a b) ∧
        ⟪a cut.label, cut.exit⟫ = b cut.label) ∧
      Route (Adj (clipSet Q a b))
        (D + ((clipRepairCutLegs legs).map fun leg =>
          B leg.label leg.entry leg.exit).sum) u v := by
  obtain ⟨x, hx, hux⟩ := HirschClipLift.endpoint_lift_to_outer_vertex Q hQc hQ a b u hu
  obtain ⟨y, hy, hvy⟩ := HirschClipLift.endpoint_lift_to_outer_vertex Q hQc hQ a b v hv
  exact route_clip_of_lifted_endpoints_with_pair_specific_cut_legs
    Q hQc hQ a b D B hFaces o ho hstrict u v hu hv x y hx hy hux hvy (hD x hx y hy)

#print axioms clipRepairPairCost_sum_eq_cut_add_old_length
#print axioms route_clip_of_lifted_endpoints_with_pair_specific_cut_legs
#print axioms route_clip_with_pair_specific_cut_legs

end HirschRadial
