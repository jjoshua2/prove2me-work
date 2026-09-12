import Solutions.PolynomialTargetConeBatchReinsertion
import Solutions.PolynomialSimultaneousClipUsedCuts

/-!
Path-sensitive target-cone batch reinsertion.

The existing target-cone theorem charges every target-slack row in the batch.
This refinement returns, separately for each routed endpoint pair, a simple
`Nodup` list of the target-slack rows whose final cut faces were actually used
by the radial repair route. Pairwise routes pay two outer star edges plus only
those face budgets; target-rooted routes pay one outer star edge plus only those
face budgets.

No bound on the selected face costs is asserted here.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRegionRoute

set_option autoImplicit false
set_option maxHeartbeats 7000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschTargetDeletion

/-- Restore all target-slack rows simultaneously, but charge only the distinct
final cut faces actually used by the repaired route. -/
theorem target_slack_batch_reinsertion_with_parent_routes_used_cuts
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (J : Finset (Fin n))
    (hJ : ∀ i, i ∈ J ↔ ⟪a i, v⟫ < b i)
    (B : Fin n → ℕ)
    (hFaces : ∀ i ∈ J, ∀ p ∈ extremePoints ℝ (Hpoly a b),
      ⟪a i, p⟫ = b i → ∀ q ∈ extremePoints ℝ (Hpoly a b),
      ⟪a i, q⟫ = b i → Route (Adj (Hpoly a b)) (B i) p q) :
    (∀ u ∈ extremePoints ℝ (Hpoly a b),
      ∀ z ∈ extremePoints ℝ (Hpoly a b),
        ∃ cuts : List J,
          cuts.Nodup ∧
          Route (Adj (Hpoly a b))
            (2 + (cuts.map (fun i => B i.1)).sum) u z) ∧
    (∀ u ∈ extremePoints ℝ (Hpoly a b),
      ∃ cuts : List J,
        cuts.Nodup ∧
        Route (Adj (Hpoly a b))
          (1 + (cuts.map (fun i => B i.1)).sum) v u) := by
  classical
  obtain ⟨m, _hcount, e, hret, _hinj, _hvOuter, _huncappedRecover⟩ :=
    exists_target_preserving_batch_deletion a b v hv J (fun i hi => (hJ i).mp hi)
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
    exists_compact_star_cap_of_target_tight_selection a b v hv hbd e hcover htight
  let Q := HirschPointed.injectiveCappedHpoly
    (fun k => a (e k)) (fun k => b (e k)) M
  let aj : J → EuclideanSpace ℝ (Fin d) := fun i => a i.1
  let bj : J → ℝ := fun i => b i.1
  let Bj : J → ℕ := fun i => B i.1
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
  have hstrict : ∀ i : J, ⟪aj i, v⟫ < bj i := fun i => (hJ i.1).mp i.2
  have hFaces' : ∀ i : J,
      ∀ p ∈ extremePoints ℝ (HirschRadial.clipSet Q aj bj),
        ⟪aj i, p⟫ = bj i →
      ∀ q ∈ extremePoints ℝ (HirschRadial.clipSet Q aj bj),
        ⟪aj i, q⟫ = bj i →
      Route (Adj (HirschRadial.clipSet Q aj bj)) (Bj i) p q := by
    intro i p hp hpi q hq hqi
    rw [hrecover] at hp hq ⊢
    exact hFaces i.1 i.2 p hp hpi q hq hqi
  have hvP : v ∈ extremePoints ℝ (HirschRadial.clipSet Q aj bj) := by
    rw [hrecover]
    exact hv
  have hroot : ∀ z ∈ extremePoints ℝ Q, Route (Adj Q) 1 v z := by
    intro z hz
    apply route_one
    rcases hstar z hz with heq | hedge
    · exact Or.inl heq.symm
    · exact Or.inr hedge
  constructor
  · intro u hu z hz
    have huP : u ∈ extremePoints ℝ (HirschRadial.clipSet Q aj bj) := by
      rw [hrecover]
      exact hu
    have hzP : z ∈ extremePoints ℝ (HirschRadial.clipSet Q aj bj) := by
      rw [hrecover]
      exact hz
    obtain ⟨x, hx, hux⟩ :=
      HirschClipLift.endpoint_lift_to_outer_vertex Q hQc hQ aj bj u huP
    obtain ⟨y, hy, hzy⟩ :=
      HirschClipLift.endpoint_lift_to_outer_vertex Q hQc hQ aj bj z hzP
    obtain ⟨cuts, hcuts, hr⟩ :=
      HirschRadial.route_clip_of_lifted_endpoints_with_parent_routes_used_cuts
        Q hQc hQ aj bj Bj hFaces' v hvQ.1 hstrict
        u z huP hzP x y hx hy hux hzy (hdiam x hx y hy)
    refine ⟨cuts, hcuts, ?_⟩
    simpa only [hrecover, Bj] using hr
  · intro u hu
    have huP : u ∈ extremePoints ℝ (HirschRadial.clipSet Q aj bj) := by
      rw [hrecover]
      exact hu
    obtain ⟨y, hy, huy⟩ :=
      HirschClipLift.endpoint_lift_to_outer_vertex Q hQc hQ aj bj u huP
    obtain ⟨cuts, hcuts, hr⟩ :=
      HirschRadial.route_clip_of_lifted_endpoints_with_parent_routes_used_cuts
        Q hQc hQ aj bj Bj hFaces' v hvQ.1 hstrict
        v u hvP huP v y hvQ hy (Or.inl rfl) huy (hroot y hy)
    refine ⟨cuts, hcuts, ?_⟩
    simpa only [hrecover, Bj] using hr

#print axioms target_slack_batch_reinsertion_with_parent_routes_used_cuts

end HirschTargetDeletion
