import Mathlib
import Solutions.PolynomialCurrentExteriorCapRouting
import Solutions.PolynomialParentRouteClosedFaceTrace

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 6000000

noncomputable section
namespace HirschExteriorCurrent

open HirschRegionRoute

variable {d : ℕ}

/-- Variant of the current exterior-cap repair in which the final cut face is
charged by an ambient parent-edge routing budget, rather than by intrinsic
`DiamLE` of the face.

This is strictly the interface needed by same-excess/lower-dimension facet
reduction: the replacement route may leave the facet, as long as it remains a
parent edge walk. -/
theorem diamLE_single_clip_of_augmented_outer_routes_with_parent_face_route
    (Q G : Set (EuclideanSpace ℝ (Fin d)))
    (hQc : IsCompact Q) (hQ : Convex ℝ Q)
    (a : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    (o : EuclideanSpace ℝ (Fin d)) (ho : o ∈ Q) (hstrict : ⟪a, o⟫ < b)
    (D B : ℕ)
    (hAug : ∀ x ∈ extremePoints ℝ Q, ∀ y ∈ extremePoints ℝ Q,
      Route (AugStep Q G) D x y)
    (hFaceRoute :
      ∀ u ∈ extremePoints ℝ
          (HirschRadial.clipSet Q (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)),
        ⟪a, u⟫ = b →
      ∀ v ∈ extremePoints ℝ
          (HirschRadial.clipSet Q (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)),
        ⟪a, v⟫ = b →
        Route
          (Adj (HirschRadial.clipSet Q (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)))
          B u v)
    (hShadow : ∀ x ∈ G, ∀ y ∈ G, ∀ z ∈ segment ℝ x y,
      HirschRadial.retract (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) o z ∈
        HirschRadial.clipSet Q (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) ∩
          {p | ⟪a, p⟫ = b}) :
    DiamLE (HirschRadial.clipSet Q (fun _ : Fin 1 => a) (fun _ : Fin 1 => b))
      (D + B) := by
  classical
  let aa : Fin 1 → EuclideanSpace ℝ (Fin d) := fun _ => a
  let bb : Fin 1 → ℝ := fun _ => b
  let P := HirschRadial.clipSet Q aa bb
  let F : Set (EuclideanSpace ℝ (Fin d)) := P ∩ {z | ⟪a, z⟫ = b}
  have hPc : IsCompact P := HirschRadial.clipSet_compact Q hQc aa bb
  have hPv : Convex ℝ P := HirschRadial.clipSet_convex Q hQ aa bb
  have hstrict' : ∀ i : Fin 1, ⟪aa i, o⟫ < bb i := by intro i; exact hstrict
  intro u hu v hv
  obtain ⟨x, hx, hux⟩ :=
    HirschClipLift.endpoint_lift_to_outer_vertex Q hQc hQ aa bb u hu
  obtain ⟨y, hy, hvy⟩ :=
    HirschClipLift.endpoint_lift_to_outer_vertex Q hQc hQ aa bb v hv
  obtain ⟨w, hw0, hwD, hstep⟩ := hAug x hx y hy
  have hwv : ∀ k ≤ D, w k ∈ extremePoints ℝ Q := by
    intro k hk
    induction k with
    | zero => simpa [hw0] using hx
    | succ k ih =>
        have hkD : k < D := by omega
        rcases hstep k hkD with heq | hrel
        · rw [← heq]
          exact ih (by omega)
        · rcases hrel with hedge | hcap
          · exact HirschPolynomialAccess.adj_right_extreme Q hedge
          · exact hcap.2.1
  let E : Fin D → Set (EuclideanSpace ℝ (Fin d)) := fun k =>
    if w k.val = w (k.val + 1) ∨ Adj Q (w k.val) (w (k.val + 1)) then
      P ∩ segment ℝ (w k.val) (w (k.val + 1)) else ∅
  have hEext : ∀ k : Fin D, IsExtreme ℝ P (E k) := by
    intro k
    by_cases hold : w k.val = w (k.val + 1) ∨ Adj Q (w k.val) (w (k.val + 1))
    · rw [show E k = P ∩ segment ℝ (w k.val) (w (k.val + 1)) by simp [E, hold]]
      have hseg : IsExtreme ℝ Q (segment ℝ (w k.val) (w (k.val + 1))) := by
        rcases hold with heq | hadj
        · rw [heq, segment_same]
          exact isExtreme_singleton.mpr (hwv (k.val + 1) (by omega))
        · exact hadj.2
      exact HirschSubsegment.extreme_inter_of_parent_subset Q P _
        inter_subset_left hseg
    · rw [show E k = ∅ by simp [E, hold]]
      exact ⟨empty_subset _, by intro x hx y hy z hz; exact False.elim hz⟩
  have hEclosed : ∀ k : Fin D, IsClosed (E k) := by
    intro k
    by_cases hold : w k.val = w (k.val + 1) ∨ Adj Q (w k.val) (w (k.val + 1))
    · rw [show E k = P ∩ segment ℝ (w k.val) (w (k.val + 1)) by simp [E, hold]]
      have hc : IsCompact (segment ℝ (w k.val) (w (k.val + 1))) := by
        rw [segment_eq_image]
        exact isCompact_Icc.image (by fun_prop)
      exact hPc.isClosed.inter hc.isClosed
    · simpa [E, hold] using
        (isClosed_empty : IsClosed (∅ : Set (EuclideanSpace ℝ (Fin d))))
  have hED : ∀ k : Fin D, DiamLE (E k) 1 := by
    intro k
    by_cases hold : w k.val = w (k.val + 1) ∨ Adj Q (w k.val) (w (k.val + 1))
    · rw [show E k = P ∩ segment ℝ (w k.val) (w (k.val + 1)) by simp [E, hold]]
      exact HirschSubsegment.diamLE_of_convex_subsegment _
        (hPv.inter (convex_segment _ _)) _ _ inter_subset_right
    · rw [show E k = ∅ by simp [E, hold]]
      simp [DiamLE]
  let S : Sum (Fin D) (Sum (Fin 1) (Fin 2)) → Set (EuclideanSpace ℝ (Fin d))
    | .inl k => E k
    | .inr (.inl _) => F
    | .inr (.inr k) => {if k = 0 then u else v}
  let C : Sum (Fin D) (Sum (Fin 1) (Fin 2)) → ℕ
    | .inl _ => 1
    | .inr (.inl _) => B
    | .inr (.inr _) => 0
  have hSext : ∀ i, IsExtreme ℝ P (S i) := by
    intro i
    rcases i with k | (q | t)
    · exact hEext k
    · exact HirschClipLift.supporting_equality_extreme P a b
        (fun z hz => hz.2 0)
    · by_cases ht : t = 0
      · simpa [S, ht] using (isExtreme_singleton.mpr hu)
      · simpa [S, ht] using (isExtreme_singleton.mpr hv)
  have hSclosed : ∀ i, IsClosed (S i) := by
    intro i
    rcases i with k | (q | t)
    · exact hEclosed k
    · exact hPc.isClosed.inter (isClosed_eq (by fun_prop) continuous_const)
    · exact isClosed_singleton
  have hSroute : ∀ i,
      ∀ p ∈ extremePoints ℝ P ∩ S i,
      ∀ q ∈ extremePoints ℝ P ∩ S i,
        Route (Adj P) (C i) p q := by
    intro i p hp q hq
    rcases i with k | (r | t)
    · have hpE : p ∈ extremePoints ℝ P ∩ E k := by simpa [S] using hp
      have hqE : q ∈ extremePoints ℝ P ∩ E k := by simpa [S] using hq
      simpa [C] using
        (HirschRegionRoute.extreme_face_region P (E k) 1 (hEext k) (hED k)
          p hpE q hqE)
    · have hpF : p ∈ F := by simpa [S] using hp.2
      have hqF : q ∈ F := by simpa [S] using hq.2
      have hroute := hFaceRoute p (by simpa [P, aa, bb] using hp.1) hpF.2
        q (by simpa [P, aa, bb] using hq.1) hqF.2
      simpa [C, P, aa, bb] using hroute
    · have hp0 : p = (if t = 0 then u else v) := by simpa [S] using hp.2
      have hq0 : q = (if t = 0 then u else v) := by simpa [S] using hq.2
      have hpq : p = q := hp0.trans hq0.symm
      subst q
      have hzero : Route (Adj P) 0 p p :=
        ⟨fun _ => p, rfl, rfl, by intro j hj; omega⟩
      simpa [C] using hzero
  let ρ := HirschRadial.retract aa bb o
  have hρP : ∀ z ∈ Q, ρ z ∈ P :=
    fun z hz => HirschRadial.retract_mem Q hQ aa bb o z ho hz hstrict'
  have hρfix : ∀ z ∈ P, ρ z = z := by
    intro z hz
    exact HirschRadial.retract_fixes aa bb o z hstrict' hz.2
  have hspoke : ∀ (e z : EuclideanSpace ℝ (Fin d)), e ∈ P → z ∈ Q →
      (e = z ∨ ∃ i : Fin 1, ⟪aa i, e⟫ = bb i ∧ bb i ≤ ⟪aa i, z⟫) →
      (∃ k : Fin 2, e = if k = 0 then u else v) →
      ∀ t ∈ segment ℝ e z, ∃ i, ρ t ∈ S i := by
    intro e z he hz hez hend t ht
    rcases hez with heq | ⟨i, hei, hzi⟩
    · have hte : t = e := by simpa [← heq] using ht
      obtain ⟨k, hk⟩ := hend
      refine ⟨.inr (.inr k), ?_⟩
      change ρ t = if k = 0 then u else v
      exact (congrArg ρ hte).trans ((hρfix e he).trans hk)
    · have htQ : t ∈ Q := hQ.segment_subset he.1 hz ht
      have hit : bb i ≤ ⟪aa i, t⟫ := by
        obtain ⟨α, β, hα, hβ, hsum, heval⟩ := ht
        have hev := congrArg (fun q : EuclideanSpace ℝ (Fin d) => ⟪aa i, q⟫) heval
        simp only [inner_add_right, inner_smul_right] at hev
        have htotal : α * bb i + β * bb i = bb i := by
          rw [← add_mul, hsum, one_mul]
        rw [hei] at hev
        linarith [mul_le_mul_of_nonneg_left hzi hβ]
      obtain ⟨q, hq⟩ :=
        HirschRadial.retract_on_cut_of_exceeded aa bb o t hstrict' i hit
      have hq0 : q = 0 := Subsingleton.elim _ _
      refine ⟨.inr (.inl 0), hρP t htQ, ?_⟩
      simpa [F, aa, bb, hq0] using hq
  have hleft : ∀ t ∈ segment ℝ u x, ∃ i, ρ t ∈ S i :=
    hspoke u x hu.1 hx.1 hux ⟨0, by simp⟩
  have hright : ∀ t ∈ segment ℝ v y, ∃ i, ρ t ∈ S i :=
    hspoke v y hv.1 hy.1 hvy ⟨1, by simp⟩
  have htrace : ∀ L ≤ D, ∀ z ∈ HirschRadial.walkTrace w L, ∃ i, ρ z ∈ S i := by
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
        · have hk : L < D := by omega
          rcases hstep L hk with heq | hrel
          · have htQ : z ∈ Q :=
              hQ.segment_subset (hwv L (by omega)).1 (hwv (L + 1) (by omega)).1 hz
            have hPz := hρP z htQ
            rcases HirschRadial.retract_eq_self_or_on_cut aa bb o z hstrict' with
              hfix | ⟨q, hq⟩
            · have hfix' : ρ z = z := by simpa [ρ] using hfix
              refine ⟨.inl ⟨L, hk⟩, ?_⟩
              change ρ z ∈ if w L = w (L + 1) ∨ Adj Q (w L) (w (L + 1)) then
                P ∩ segment ℝ (w L) (w (L + 1)) else ∅
              rw [if_pos (Or.inl heq)]
              exact ⟨hPz, by simpa [hfix'] using hz⟩
            · have hq0 : q = 0 := Subsingleton.elim _ _
              exact ⟨.inr (.inl 0), hPz, by simpa [F, aa, bb, hq0] using hq⟩
          · rcases hrel with hedge | hcap
            · have htQ : z ∈ Q := hedge.2.subset hz
              have hPz := hρP z htQ
              rcases HirschRadial.retract_eq_self_or_on_cut aa bb o z hstrict' with
                hfix | ⟨q, hq⟩
              · have hfix' : ρ z = z := by simpa [ρ] using hfix
                refine ⟨.inl ⟨L, hk⟩, ?_⟩
                change ρ z ∈ if w L = w (L + 1) ∨ Adj Q (w L) (w (L + 1)) then
                  P ∩ segment ℝ (w L) (w (L + 1)) else ∅
                rw [if_pos (Or.inr hedge)]
                exact ⟨hPz, by simpa [hfix'] using hz⟩
              · have hq0 : q = 0 := Subsingleton.elim _ _
                exact ⟨.inr (.inl 0), hPz, by simpa [F, aa, bb, hq0] using hq⟩
            · have hs := hShadow (w L) hcap.2.2.1 (w (L + 1)) hcap.2.2.2 z hz
              exact ⟨.inr (.inl 0), by simpa [F, P, aa, bb, ρ] using hs⟩
  let K := (segment ℝ u x ∪ HirschRadial.walkTrace w D) ∪ segment ℝ v y
  have hK : IsPreconnected K := by
    have h1 : IsPreconnected (segment ℝ u x ∪ HirschRadial.walkTrace w D) :=
      (convex_segment u x).isPreconnected.union x (right_mem_segment ℝ _ _)
        (by simpa [hw0] using HirschRadial.walkTrace_start w D)
        (HirschRadial.walkTrace_preconnected w D)
    exact h1.union y (Or.inr (by simpa [hwD] using HirschRadial.walkTrace_end w D))
      (right_mem_segment ℝ _ _) (convex_segment v y).isPreconnected
  have himage : IsPreconnected (ρ '' K) :=
    hK.image ρ (HirschRadial.continuous_retract aa bb o).continuousOn
  have hcover : ∀ z ∈ ρ '' K, ∃ i, z ∈ S i := by
    rintro z ⟨q, hq, rfl⟩
    rcases hq with (hq | hq) | hq
    · exact hleft q hq
    · exact htrace D (le_refl _) q hq
    · exact hright q hq
  have huK : u ∈ ρ '' K :=
    ⟨u, Or.inl (Or.inl (left_mem_segment ℝ _ _)), hρfix u hu.1⟩
  have hvK : v ∈ ρ '' K :=
    ⟨v, Or.inr (left_mem_segment ℝ _ _), hρfix v hv.1⟩
  have hr := HirschRegionRoute.route_of_preconnected_face_cover_with_parent_routes
    P S C hPc hSext hSclosed hSroute (ρ '' K) himage hcover u v hu hv huK hvK
  simpa [C, Fintype.sum_sum_type, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using hr

/-- Combine old-vertex routes and cap classification with the ambient-face-route
repair.  The only numerical inputs are the old-vertex graph cost `D` and an
ambient parent-edge budget `B` between vertices on the final cut face. -/
theorem diamLE_single_clip_of_old_routes_and_cap_classification_with_parent_face_route
    (Q G V : Set (EuclideanSpace ℝ (Fin d)))
    (hQc : IsCompact Q) (hQ : Convex ℝ Q)
    (a : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    (o : EuclideanSpace ℝ (Fin d)) (ho : o ∈ Q) (hstrict : ⟪a, o⟫ < b)
    (D B : ℕ)
    (hOld : ∀ x ∈ V, ∀ y ∈ V, Route (Adj Q) D x y)
    (hclass : ∀ x ∈ extremePoints ℝ Q,
      x ∈ V ∨ (x ∈ G ∧ ∃ y ∈ V, Adj Q y x))
    (hFaceRoute :
      ∀ u ∈ extremePoints ℝ
          (HirschRadial.clipSet Q (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)),
        ⟪a, u⟫ = b →
      ∀ v ∈ extremePoints ℝ
          (HirschRadial.clipSet Q (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)),
        ⟪a, v⟫ = b →
        Route
          (Adj (HirschRadial.clipSet Q (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)))
          B u v)
    (hShadow : ∀ x ∈ G, ∀ y ∈ G, ∀ z ∈ segment ℝ x y,
      HirschRadial.retract (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) o z ∈
        HirschRadial.clipSet Q (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) ∩
          {p | ⟪a, p⟫ = b}) :
    DiamLE (HirschRadial.clipSet Q (fun _ : Fin 1 => a) (fun _ : Fin 1 => b))
      (D + 1 + B) := by
  have hAug := augmented_route_bound_of_cap_classification Q G V D hOld hclass
  simpa [Nat.add_assoc] using
    diamLE_single_clip_of_augmented_outer_routes_with_parent_face_route
      Q G hQc hQ a b o ho hstrict (D + 1) B hAug hFaceRoute hShadow

#print axioms diamLE_single_clip_of_augmented_outer_routes_with_parent_face_route
#print axioms diamLE_single_clip_of_old_routes_and_cap_classification_with_parent_face_route

end HirschExteriorCurrent
