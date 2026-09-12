import Mathlib
import Solutions.PolynomialSimultaneousClipParentRoutes
import Solutions.PolynomialUsedRegionRouting

/-!
Path-sensitive simultaneous clipping.

The earlier parent-route repair pads every repaired route to the outer route
budget plus the sum of all final cut-face budgets.  This module exposes the
actual simple region path produced by the same radial trace construction.
Its labels distinguish:

* final cut faces, charged by `B i`;
* surviving pieces of the chosen outer edge walk, charged by one;
* the two endpoint-lift singletons, charged by zero.

The returned label list is `Nodup`.  We then project that mixed support to a
`Nodup` list of cut labels, prove the exact cost decomposition, and absorb only
the distinct old-edge labels into the original outer budget `D`.  Thus the
clean path-sensitive output costs `D + sum B` over the cut faces actually used,
not over every available cut.

No polynomial bound on the selected face budgets is asserted.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRegionRoute

set_option autoImplicit false
set_option maxHeartbeats 7000000

noncomputable section
namespace HirschRadial

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- Cost of one label in the path-sensitive simultaneous-clip repair graph.
Cut faces carry their supplied parent-route budgets, old outer-edge pieces cost
one, and endpoint-lift singleton regions cost zero. -/
def clipRepairRegionCost {D : ℕ} (B : ι → ℕ) :
    Sum ι (Sum (Fin D) (Fin 2)) → ℕ
  | .inl i => B i
  | .inr (.inl _) => 1
  | .inr (.inr _) => 0

/-- Cut-face labels extracted from a mixed repair-region support list. -/
def clipRepairCutLabels {D : ℕ}
    (l : List (Sum ι (Sum (Fin D) (Fin 2)))) : List ι :=
  l.filterMap fun
    | .inl i => some i
    | .inr _ => none

/-- Old outer-edge labels extracted from a mixed repair-region support list. -/
def clipRepairOldEdgeLabels {D : ℕ}
    (l : List (Sum ι (Sum (Fin D) (Fin 2)))) : List (Fin D) :=
  l.filterMap fun
    | .inr (.inl k) => some k
    | _ => none

/-- Projecting a duplicate-free mixed repair support to cut labels preserves
`Nodup`. -/
theorem clipRepairCutLabels_nodup {D : ℕ}
    {l : List (Sum ι (Sum (Fin D) (Fin 2)))} (hl : l.Nodup) :
    (clipRepairCutLabels l).Nodup := by
  unfold clipRepairCutLabels
  apply hl.filterMap
  intro x y z hx hy
  rcases x with i | x <;> rcases y with j | y <;> simp_all

/-- Projecting a duplicate-free mixed repair support to old outer-edge labels
also preserves `Nodup`. -/
theorem clipRepairOldEdgeLabels_nodup {D : ℕ}
    {l : List (Sum ι (Sum (Fin D) (Fin 2)))} (hl : l.Nodup) :
    (clipRepairOldEdgeLabels l).Nodup := by
  unfold clipRepairOldEdgeLabels
  apply hl.filterMap
  intro x y z hx hy
  rcases x with i | (k | t) <;> rcases y with j | (k' | t') <;> simp_all

/-- Exact arithmetic decomposition of a mixed repair support: cut-face budgets
plus one unit for each used old outer edge. Endpoint singleton labels vanish. -/
theorem clipRepairRegionCost_sum_eq_cut_add_old_length {D : ℕ}
    (B : ι → ℕ) (l : List (Sum ι (Sum (Fin D) (Fin 2)))) :
    (l.map (clipRepairRegionCost (D := D) B)).sum =
      ((clipRepairCutLabels l).map B).sum + (clipRepairOldEdgeLabels l).length := by
  induction l with
  | nil =>
      simp [clipRepairRegionCost, clipRepairCutLabels, clipRepairOldEdgeLabels]
  | cons x xs ih =>
      rcases x with i | (k | t)
      · simp [clipRepairRegionCost, clipRepairCutLabels, clipRepairOldEdgeLabels, ih,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · simp [clipRepairRegionCost, clipRepairCutLabels, clipRepairOldEdgeLabels, ih,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · simp [clipRepairRegionCost, clipRepairCutLabels, clipRepairOldEdgeLabels, ih]

/-- A duplicate-free mixed support can use at most all `D` old outer-edge
labels. -/
theorem clipRepairOldEdgeLabels_length_le {D : ℕ}
    {l : List (Sum ι (Sum (Fin D) (Fin 2)))} (hl : l.Nodup) :
    (clipRepairOldEdgeLabels l).length ≤ D := by
  have hnd : (clipRepairOldEdgeLabels l).Nodup :=
    clipRepairOldEdgeLabels_nodup hl
  simpa using hnd.length_le_card

/-- Pairwise simultaneous clipping, exposing the exact simple region support
used by the radial repair rather than padding to every cut label.

The hypotheses and geometric construction are the same as
`route_clip_of_lifted_endpoints_with_parent_routes`.  The only strengthened
output is the `Nodup` list of actually used repair regions together with the
route whose length is exactly the sum of their region costs. -/
theorem route_clip_of_lifted_endpoints_with_parent_routes_used_regions
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
      Route (Adj (clipSet Q a b))
        ((l.map (clipRepairRegionCost (D := D) B)).sum) u v := by
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
  have hlocal : ∀ k, ∀ p ∈ extremePoints ℝ P ∩ F k,
      ∀ q ∈ extremePoints ℝ P ∩ F k, Route (Adj P) (C k) p q := by
    intro k
    rcases k with i | (e | t)
    · intro p hp q hq
      exact hFaces i p hp.1 hp.2.2 q hq.1 hq.2.2
    · exact extreme_face_region P (F (.inr (.inl e))) 1 (hF (.inr (.inl e)))
        (HirschSubsegment.diamLE_of_convex_subsegment _
          (hPv.inter (convex_segment _ _)) _ _ inter_subset_right)
    · exact extreme_face_region P (F (.inr (.inr t))) 0 (hF (.inr (.inr t)))
        (singleton_diamLE_zero _)
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
  obtain ⟨l, hnd, hr⟩ :=
    route_of_preconnected_face_cover_with_parent_routes_used_labels
      P F C hPc hF hFc hlocal (ρ '' K) himage hcover u v hu hv huK hvK
  refine ⟨l, hnd, ?_⟩
  simpa [C, clipRepairRegionCost] using hr

/-- Project the exact mixed repair support to the distinct cut faces actually
used.  All old-edge pieces fit inside the original outer budget `D`; endpoint
singletons cost zero. -/
theorem route_clip_of_lifted_endpoints_with_parent_routes_used_cut_faces
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
    ∃ cuts : List ι,
      cuts.Nodup ∧
      Route (Adj (clipSet Q a b)) (D + (cuts.map B).sum) u v := by
  obtain ⟨l, hnd, hr⟩ :=
    route_clip_of_lifted_endpoints_with_parent_routes_used_regions
      Q hQc hQ a b D B hFaces o ho hstrict u v hu hv x y hx hy hux hvy hwalk
  let cuts := clipRepairCutLabels l
  have hcuts : cuts.Nodup := by
    dsimp [cuts]
    exact clipRepairCutLabels_nodup hnd
  have hold : (clipRepairOldEdgeLabels l).length ≤ D :=
    clipRepairOldEdgeLabels_length_le hnd
  have hcost := clipRepairRegionCost_sum_eq_cut_add_old_length B l
  have hle :
      (l.map (clipRepairRegionCost (D := D) B)).sum ≤
        D + (cuts.map B).sum := by
    rw [hcost]
    dsimp [cuts]
    omega
  obtain ⟨w, hw0, hwL, hstep⟩ := hr
  exact ⟨cuts, hcuts,
    HirschProduct.pad_walk (Adj (clipSet Q a b)) hle w hw0 hwL hstep⟩

/-- Endpoint-lifted path-sensitive interface retaining the raw mixed repair
regions. -/
theorem route_clip_with_parent_routes_used_regions
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQc : IsCompact Q) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (D : ℕ) (B : ι → ℕ) (hD : DiamLE Q D)
    (hFaces : ∀ i, ∀ p ∈ extremePoints ℝ (clipSet Q a b),
      ⟪a i, p⟫ = b i → ∀ q ∈ extremePoints ℝ (clipSet Q a b),
      ⟪a i, q⟫ = b i → Route (Adj (clipSet Q a b)) (B i) p q)
    (o : EuclideanSpace ℝ (Fin d)) (ho : o ∈ Q)
    (hstrict : ∀ i, ⟪a i, o⟫ < b i)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (clipSet Q a b))
    (hv : v ∈ extremePoints ℝ (clipSet Q a b)) :
    ∃ l : List (Sum ι (Sum (Fin D) (Fin 2))),
      l.Nodup ∧
      Route (Adj (clipSet Q a b))
        ((l.map (clipRepairRegionCost (D := D) B)).sum) u v := by
  obtain ⟨x, hx, hux⟩ := HirschClipLift.endpoint_lift_to_outer_vertex Q hQc hQ a b u hu
  obtain ⟨y, hy, hvy⟩ := HirschClipLift.endpoint_lift_to_outer_vertex Q hQc hQ a b v hv
  exact route_clip_of_lifted_endpoints_with_parent_routes_used_regions
    Q hQc hQ a b D B hFaces o ho hstrict u v hu hv x y hx hy hux hvy (hD x hx y hy)

/-- Endpoint-lifted clean form: each pair of clipped vertices uses a distinct
list of cut faces and pays only the outer budget plus those face budgets. -/
theorem route_clip_with_parent_routes_used_cut_faces
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQc : IsCompact Q) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (D : ℕ) (B : ι → ℕ) (hD : DiamLE Q D)
    (hFaces : ∀ i, ∀ p ∈ extremePoints ℝ (clipSet Q a b),
      ⟪a i, p⟫ = b i → ∀ q ∈ extremePoints ℝ (clipSet Q a b),
      ⟪a i, q⟫ = b i → Route (Adj (clipSet Q a b)) (B i) p q)
    (o : EuclideanSpace ℝ (Fin d)) (ho : o ∈ Q)
    (hstrict : ∀ i, ⟪a i, o⟫ < b i)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (clipSet Q a b))
    (hv : v ∈ extremePoints ℝ (clipSet Q a b)) :
    ∃ cuts : List ι,
      cuts.Nodup ∧
      Route (Adj (clipSet Q a b)) (D + (cuts.map B).sum) u v := by
  obtain ⟨x, hx, hux⟩ := HirschClipLift.endpoint_lift_to_outer_vertex Q hQc hQ a b u hu
  obtain ⟨y, hy, hvy⟩ := HirschClipLift.endpoint_lift_to_outer_vertex Q hQc hQ a b v hv
  exact route_clip_of_lifted_endpoints_with_parent_routes_used_cut_faces
    Q hQc hQ a b D B hFaces o ho hstrict u v hu hv x y hx hy hux hvy (hD x hx y hy)

/-- Rooted path-sensitive version retaining the raw mixed repair regions. -/
theorem route_clip_from_root_with_parent_routes_used_regions
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQc : IsCompact Q) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (D : ℕ) (B : ι → ℕ)
    (hFaces : ∀ i, ∀ p ∈ extremePoints ℝ (clipSet Q a b),
      ⟪a i, p⟫ = b i → ∀ q ∈ extremePoints ℝ (clipSet Q a b),
      ⟪a i, q⟫ = b i → Route (Adj (clipSet Q a b)) (B i) p q)
    (o : EuclideanSpace ℝ (Fin d))
    (hoQ : o ∈ extremePoints ℝ Q) (hoP : o ∈ extremePoints ℝ (clipSet Q a b))
    (hstrict : ∀ i, ⟪a i, o⟫ < b i)
    (hRoot : ∀ y ∈ extremePoints ℝ Q, Route (Adj Q) D o y)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (clipSet Q a b)) :
    ∃ l : List (Sum ι (Sum (Fin D) (Fin 2))),
      l.Nodup ∧
      Route (Adj (clipSet Q a b))
        ((l.map (clipRepairRegionCost (D := D) B)).sum) o v := by
  obtain ⟨y, hy, hvy⟩ := HirschClipLift.endpoint_lift_to_outer_vertex Q hQc hQ a b v hv
  exact route_clip_of_lifted_endpoints_with_parent_routes_used_regions
    Q hQc hQ a b D B hFaces o hoQ.1 hstrict o v hoP hv o y hoQ hy
    (Or.inl rfl) hvy (hRoot y hy)

/-- Rooted clean form: only the distinct cut faces actually used by the repair
are charged beyond the rooted outer budget. -/
theorem route_clip_from_root_with_parent_routes_used_cut_faces
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQc : IsCompact Q) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (D : ℕ) (B : ι → ℕ)
    (hFaces : ∀ i, ∀ p ∈ extremePoints ℝ (clipSet Q a b),
      ⟪a i, p⟫ = b i → ∀ q ∈ extremePoints ℝ (clipSet Q a b),
      ⟪a i, q⟫ = b i → Route (Adj (clipSet Q a b)) (B i) p q)
    (o : EuclideanSpace ℝ (Fin d))
    (hoQ : o ∈ extremePoints ℝ Q) (hoP : o ∈ extremePoints ℝ (clipSet Q a b))
    (hstrict : ∀ i, ⟪a i, o⟫ < b i)
    (hRoot : ∀ y ∈ extremePoints ℝ Q, Route (Adj Q) D o y)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (clipSet Q a b)) :
    ∃ cuts : List ι,
      cuts.Nodup ∧
      Route (Adj (clipSet Q a b)) (D + (cuts.map B).sum) o v := by
  obtain ⟨y, hy, hvy⟩ := HirschClipLift.endpoint_lift_to_outer_vertex Q hQc hQ a b v hv
  exact route_clip_of_lifted_endpoints_with_parent_routes_used_cut_faces
    Q hQc hQ a b D B hFaces o hoQ.1 hstrict o v hoP hv o y hoQ hy
    (Or.inl rfl) hvy (hRoot y hy)

#print axioms clipRepairRegionCost_sum_eq_cut_add_old_length
#print axioms route_clip_of_lifted_endpoints_with_parent_routes_used_regions
#print axioms route_clip_of_lifted_endpoints_with_parent_routes_used_cut_faces
#print axioms route_clip_with_parent_routes_used_regions
#print axioms route_clip_with_parent_routes_used_cut_faces
#print axioms route_clip_from_root_with_parent_routes_used_regions
#print axioms route_clip_from_root_with_parent_routes_used_cut_faces

end HirschRadial
