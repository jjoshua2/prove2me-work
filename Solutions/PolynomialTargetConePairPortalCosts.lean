import Mathlib
import Solutions.PolynomialTargetConeUsedFaceSupport
import Solutions.PolynomialSimultaneousClipPairLegs

/-!
# Target-cone reinsertion with pair-specific portal costs

The target-tight outer is a compact star.  Restoring the rows strictly slack at
the fixed target vertex can therefore use the pair-specific simultaneous-clipping
interface with outer cost two (pairwise) or one (target-rooted).

The resulting recursive calls are no longer whole-face diameter calls.  Each is
an actual `RegionLeg` labelled by one target-slack row and carrying the concrete
parent extreme vertices at which the repaired route enters and exits that row
face.  The labels are duplicate-free and there are at most `n-d` such legs.

Thus the remaining recursive obstruction is exactly the weighted sum of costs
assigned to these actual target-slack portal pairs.  No decreasing resource for
those pair costs is claimed in this module.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRegionRoute

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschTargetDeletion

/-- A target-slack cut leg is a genuine parent-vertex pair on its labelled row
face. -/
def TargetSlackPortalLegValid {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (J : Finset (Fin n))
    (leg : RegionLeg J (EuclideanSpace ℝ (Fin d))) : Prop :=
  leg.entry ∈ extremePoints ℝ (Hpoly a b) ∧
  ⟪a leg.label.1, leg.entry⟫ = b leg.label.1 ∧
  leg.exit ∈ extremePoints ℝ (Hpoly a b) ∧
  ⟪a leg.label.1, leg.exit⟫ = b leg.label.1

/-- Target-tight batch reinsertion with costs on the actual portal pairs used.

For pairwise repair the outer star contributes two.  For target-rooted repair
it contributes one.  In either case the recursive part is a sum over a
`Nodup` list of at most `n-d` target-slack row legs, and every leg contains the
actual parent extreme entry/exit vertices on that cut face. -/
theorem target_slack_batch_reinsertion_with_pair_specific_portal_costs
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (J : Finset (Fin n))
    (hJ : ∀ i, i ∈ J ↔ ⟪a i, v⟫ < b i)
    (B : Fin n → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) → ℕ)
    (hFaces : ∀ i ∈ J, ∀ p ∈ extremePoints ℝ (Hpoly a b),
      ⟪a i, p⟫ = b i → ∀ q ∈ extremePoints ℝ (Hpoly a b),
      ⟪a i, q⟫ = b i → Route (Adj (Hpoly a b)) (B i p q) p q) :
    (∀ u ∈ extremePoints ℝ (Hpoly a b),
      ∀ w ∈ extremePoints ℝ (Hpoly a b),
        ∃ cuts : List (RegionLeg J (EuclideanSpace ℝ (Fin d))),
          (cuts.map RegionLeg.label).Nodup ∧
          cuts.length ≤ n - d ∧
          (∀ leg ∈ cuts, TargetSlackPortalLegValid a b J leg) ∧
          Route (Adj (Hpoly a b))
            (2 + (cuts.map fun leg =>
              B leg.label.1 leg.entry leg.exit).sum) u w) ∧
    (∀ u ∈ extremePoints ℝ (Hpoly a b),
        ∃ cuts : List (RegionLeg J (EuclideanSpace ℝ (Fin d))),
          (cuts.map RegionLeg.label).Nodup ∧
          cuts.length ≤ n - d ∧
          (∀ leg ∈ cuts, TargetSlackPortalLegValid a b J leg) ∧
          Route (Adj (Hpoly a b))
            (1 + (cuts.map fun leg =>
              B leg.label.1 leg.entry leg.exit).sum) v u) := by
  classical
  obtain ⟨m, _hcount, e, hret, _hinj, _hvOuter, _huncappedRecover⟩ :=
    exists_target_preserving_batch_deletion a b v hv J
      (fun i hi => (hJ i).mp hi)
  have hcover : ∀ i, ⟪a i, v⟫ = b i → ∃ k, e k = i := by
    intro i hi
    apply (hret i).mpr
    intro hiJ
    have hlt := (hJ i).mp hiJ
    rw [hi] at hlt
    exact (lt_irrefl _ hlt)
  have htight : ∀ k, ⟪a (e k), v⟫ = b (e k) := by
    intro k
    have hnot : e k ∉ J := (hret (e k)).mp ⟨k, rfl⟩
    exact le_antisymm (hv.1 (e k))
      (le_of_not_gt (fun h => hnot ((hJ (e k)).mpr h)))
  obtain ⟨M, hQc, hQ, hcontain, hvQ, hstar, hdiam⟩ :=
    exists_compact_star_cap_of_target_tight_selection
      a b v hv hbd e hcover htight
  let Q := HirschPointed.injectiveCappedHpoly
    (fun k => a (e k)) (fun k => b (e k)) M
  let aj : J → EuclideanSpace ℝ (Fin d) := fun i => a i.1
  let bj : J → ℝ := fun i => b i.1
  let Bj : J → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) → ℕ := fun i p q => B i.1 p q
  have hrecover : HirschRadial.clipSet Q aj bj = Hpoly a b := by
    ext z
    constructor
    · rintro ⟨hzQ, hcuts⟩ i
      by_cases hi : i ∈ J
      · exact hcuts ⟨i, hi⟩
      · obtain ⟨k, hk⟩ := (hret i).mpr hi
        have h := hzQ.1 k
        simpa only [hk] using h
    · intro hz
      exact ⟨hcontain hz, fun i => hz i.1⟩
  have hstrict : ∀ i : J, ⟪aj i, v⟫ < bj i :=
    fun i => (hJ i.1).mp i.2
  have hFaces' : ∀ i : J,
      ∀ p ∈ extremePoints ℝ (HirschRadial.clipSet Q aj bj),
      ⟪aj i, p⟫ = bj i →
      ∀ q ∈ extremePoints ℝ (HirschRadial.clipSet Q aj bj),
      ⟪aj i, q⟫ = bj i →
        Route (Adj (HirschRadial.clipSet Q aj bj)) (Bj i p q) p q := by
    intro i p hp hpi q hq hqi
    rw [hrecover] at hp hq ⊢
    exact hFaces i.1 i.2 p hp hpi q hq hqi
  have hroot : ∀ z ∈ extremePoints ℝ Q, Route (Adj Q) 1 v z := by
    intro z hz
    apply route_one
    rcases hstar z hz with heq | hedge
    · exact Or.inl heq.symm
    · exact Or.inr hedge
  have hvP : v ∈ extremePoints ℝ (HirschRadial.clipSet Q aj bj) := by
    rw [hrecover]
    exact hv
  have hJcard : J.card ≤ n - d := by
    have hfull : J = Finset.univ.filter (fun i => ⟪a i, v⟫ < b i) := by
      ext i
      simp [hJ i]
    rw [hfull]
    exact target_slack_rows_card_le_rowExcess a b v hv
  have hJcard' : Fintype.card J ≤ n - d := by
    simpa using hJcard
  have hcutsLength :
      ∀ {cuts : List (RegionLeg J (EuclideanSpace ℝ (Fin d)))},
        (cuts.map RegionLeg.label).Nodup → cuts.length ≤ n - d := by
    intro cuts hnd
    have hlen : (cuts.map RegionLeg.label).length ≤ Fintype.card J :=
      hnd.length_le_card
    have hlen' : cuts.length ≤ Fintype.card J := by simpa using hlen
    exact hlen'.trans hJcard'
  have valid_of_clip_valid :
      ∀ {cut : RegionLeg J (EuclideanSpace ℝ (Fin d))},
        (cut.entry ∈ extremePoints ℝ (HirschRadial.clipSet Q aj bj) ∧
          ⟪aj cut.label, cut.entry⟫ = bj cut.label ∧
          cut.exit ∈ extremePoints ℝ (HirschRadial.clipSet Q aj bj) ∧
          ⟪aj cut.label, cut.exit⟫ = bj cut.label) →
        TargetSlackPortalLegValid a b J cut := by
    intro cut hcut
    rcases hcut with ⟨hentry, htentry, hexit, htexit⟩
    rw [hrecover] at hentry hexit
    exact ⟨hentry, by simpa [aj, bj] using htentry,
      hexit, by simpa [aj, bj] using htexit⟩
  constructor
  · intro u hu w hw
    have hu' : u ∈ extremePoints ℝ (HirschRadial.clipSet Q aj bj) := by
      rw [hrecover]
      exact hu
    have hw' : w ∈ extremePoints ℝ (HirschRadial.clipSet Q aj bj) := by
      rw [hrecover]
      exact hw
    obtain ⟨legs, hnd, hvalid, hr⟩ :=
      HirschRadial.route_clip_with_pair_specific_cut_legs
        Q hQc hQ aj bj 2 Bj hdiam hFaces' v hvQ.1 hstrict
        u w hu' hw'
    let cuts : List (RegionLeg J (EuclideanSpace ℝ (Fin d))) :=
      HirschRadial.clipRepairCutLegs legs
    have hcutsNodup : (cuts.map RegionLeg.label).Nodup := by
      dsimp [cuts]
      exact HirschRadial.clipRepairCutLeg_labels_nodup hnd
    have hvalidCuts : ∀ leg ∈ cuts, TargetSlackPortalLegValid a b J leg := by
      intro leg hleg
      exact valid_of_clip_valid (hvalid leg (by simpa [cuts] using hleg))
    refine ⟨cuts, hcutsNodup, hcutsLength hcutsNodup, hvalidCuts, ?_⟩
    rw [hrecover] at hr
    simpa [cuts, Bj] using hr
  · intro u hu
    have hu' : u ∈ extremePoints ℝ (HirschRadial.clipSet Q aj bj) := by
      rw [hrecover]
      exact hu
    obtain ⟨y, hy, huy⟩ :=
      HirschClipLift.endpoint_lift_to_outer_vertex Q hQc hQ aj bj u hu'
    obtain ⟨legs, hnd, hvalid, hr⟩ :=
      HirschRadial.route_clip_of_lifted_endpoints_with_pair_specific_cut_legs
        Q hQc hQ aj bj 1 Bj hFaces' v hvQ.1 hstrict
        v u hvP hu' v y hvQ hy (Or.inl rfl) huy (hroot y hy)
    let cuts : List (RegionLeg J (EuclideanSpace ℝ (Fin d))) :=
      HirschRadial.clipRepairCutLegs legs
    have hcutsNodup : (cuts.map RegionLeg.label).Nodup := by
      dsimp [cuts]
      exact HirschRadial.clipRepairCutLeg_labels_nodup hnd
    have hvalidCuts : ∀ leg ∈ cuts, TargetSlackPortalLegValid a b J leg := by
      intro leg hleg
      exact valid_of_clip_valid (hvalid leg (by simpa [cuts] using hleg))
    refine ⟨cuts, hcutsNodup, hcutsLength hcutsNodup, hvalidCuts, ?_⟩
    rw [hrecover] at hr
    simpa [cuts, Bj] using hr

#print axioms target_slack_batch_reinsertion_with_pair_specific_portal_costs

end HirschTargetDeletion
