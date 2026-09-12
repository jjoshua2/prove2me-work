import Mathlib
import Solutions.PolynomialTargetConeBatchReinsertion
import Solutions.PolynomialTargetSlackUniformBudget
import Solutions.PolynomialSimultaneousClipPairLegs

/-!
Target-rooted specialization of pair-specific simultaneous clipping.

The target-tight outer is compactified to a true vertex star. For a fixed target
vertex `v`, one old outer edge reaches any lifted outer endpoint. Simultaneous
restoration of the target-slack cuts then charges only the actual cut-face portal
pairs used by the repair. The cut labels are duplicate-free and hence there are
at most `n-d` of them.

This removes whole-face worst-case budgets from the target-rooted interface. It
does not bound the pair-specific costs themselves.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRegionRoute

set_option autoImplicit false
set_option maxHeartbeats 7000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschTargetDeletion

/-- Target-rooted batch reinsertion with exact pair-specific cut-face costs.

For every original vertex `u`, return the actual distinct target-slack cut legs
used by the radial repair. Each leg remembers its row and its parent-vertex
entry/exit pair; both endpoints are tight on that row. The route pays one unit
for the target-cone star edge plus only the supplied costs of those actual
pairs. The number of used cut labels is at most the ambient row excess `n-d`.
-/
theorem target_slack_batch_reinsertion_with_pair_specific_cut_legs
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (B : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℕ)
    (hFaces : ∀ i : Fin n, ⟪a i, v⟫ < b i →
      ∀ p ∈ extremePoints ℝ (Hpoly a b), ⟪a i, p⟫ = b i →
      ∀ q ∈ extremePoints ℝ (Hpoly a b), ⟪a i, q⟫ = b i →
        Route (Adj (Hpoly a b)) (B i p q) p q) :
    ∀ u ∈ extremePoints ℝ (Hpoly a b),
      ∃ cuts : List
          (RegionLeg
            {i : Fin n // ⟪a i, v⟫ < b i}
            (EuclideanSpace ℝ (Fin d))),
        (cuts.map RegionLeg.label).Nodup ∧
        cuts.length ≤ n - d ∧
        (∀ cut ∈ cuts,
          cut.entry ∈ extremePoints ℝ (Hpoly a b) ∧
          ⟪a cut.label.1, cut.entry⟫ = b cut.label.1 ∧
          cut.exit ∈ extremePoints ℝ (Hpoly a b) ∧
          ⟪a cut.label.1, cut.exit⟫ = b cut.label.1) ∧
        Route (Adj (Hpoly a b))
          (1 + (cuts.map fun leg =>
            B leg.label.1 leg.entry leg.exit).sum) v u := by
  classical
  let J : Finset (Fin n) := Finset.univ.filter (fun i => ⟪a i, v⟫ < b i)
  have hJiff : ∀ i, i ∈ J ↔ ⟪a i, v⟫ < b i := by
    intro i
    simp [J]
  obtain ⟨m, _hcount, e, hret, _hinj, _hvOuter, _huncappedRecover⟩ :=
    exists_target_preserving_batch_deletion a b v hv J
      (fun i hi => (hJiff i).mp hi)
  have hcover : ∀ i, ⟪a i, v⟫ = b i → ∃ k, e k = i := by
    intro i hi
    apply (hret i).mpr
    intro hiJ
    have hlt := (hJiff i).mp hiJ
    rw [hi] at hlt
    exact (lt_irrefl _ hlt)
  have htight : ∀ k, ⟪a (e k), v⟫ = b (e k) := by
    intro k
    have hnot : e k ∉ J := (hret (e k)).mp ⟨k, rfl⟩
    exact le_antisymm (hv.1 (e k))
      (le_of_not_gt (fun h => hnot ((hJiff (e k)).mpr h)))
  obtain ⟨M, hQc, hQ, hcontain, hvQ, hstar, _hdiam⟩ :=
    exists_compact_star_cap_of_target_tight_selection
      a b v hv hbd e hcover htight
  let Q := HirschPointed.injectiveCappedHpoly
    (fun k => a (e k)) (fun k => b (e k)) M
  let I := {i : Fin n // ⟪a i, v⟫ < b i}
  let aj : I → EuclideanSpace ℝ (Fin d) := fun i => a i.1
  let bj : I → ℝ := fun i => b i.1
  let C : I → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℕ :=
    fun i p q => B i.1 p q
  have hrecover : HirschRadial.clipSet Q aj bj = Hpoly a b := by
    ext z
    constructor
    · rintro ⟨hzQ, hcuts⟩ i
      by_cases hi : ⟪a i, v⟫ < b i
      · exact hcuts ⟨i, hi⟩
      · have hiJ : i ∉ J := by simpa [hJiff]
        obtain ⟨k, hk⟩ := (hret i).mpr hiJ
        have h := hzQ.1 k
        simpa only [hk] using h
    · intro hz
      refine ⟨hcontain hz, ?_⟩
      intro i
      exact hz i.1
  have hstrict : ∀ i : I, ⟪aj i, v⟫ < bj i := fun i => i.2
  have hFaces' : ∀ i : I,
      ∀ p ∈ extremePoints ℝ (HirschRadial.clipSet Q aj bj),
        ⟪aj i, p⟫ = bj i →
      ∀ q ∈ extremePoints ℝ (HirschRadial.clipSet Q aj bj),
        ⟪aj i, q⟫ = bj i →
        Route (Adj (HirschRadial.clipSet Q aj bj)) (C i p q) p q := by
    intro i p hp hpi q hq hqi
    rw [hrecover] at hp hq ⊢
    exact hFaces i.1 i.2 p hp hpi q hq hqi
  have hvP : v ∈ extremePoints ℝ (HirschRadial.clipSet Q aj bj) := by
    rw [hrecover]
    exact hv
  intro u hu
  have huP : u ∈ extremePoints ℝ (HirschRadial.clipSet Q aj bj) := by
    rw [hrecover]
    exact hu
  obtain ⟨y, hy, huy⟩ :=
    HirschClipLift.endpoint_lift_to_outer_vertex Q hQc hQ aj bj u huP
  have hroot : Route (Adj Q) 1 v y := by
    apply route_one
    rcases hstar y hy with heq | hedge
    · exact Or.inl heq.symm
    · exact Or.inr hedge
  obtain ⟨legs, hnd, hvalid, hr⟩ :=
    HirschRadial.route_clip_of_lifted_endpoints_with_pair_specific_cut_legs
      Q hQc hQ aj bj 1 C hFaces' v hvQ.1 hstrict
      v u hvP huP v y hvQ hy (Or.inl rfl) huy hroot
  let cuts := HirschRadial.clipRepairCutLegs legs
  have hcutsNodup : (cuts.map RegionLeg.label).Nodup := by
    exact HirschRadial.clipRepairCutLeg_labels_nodup hnd
  have hcardJ : Fintype.card I ≤ n - d := by
    have hcard := target_slack_rows_card_le_rowExcess a b v hv
    simpa [I, J] using hcard
  have hlen : cuts.length ≤ n - d := by
    have hle : (cuts.map RegionLeg.label).length ≤ Fintype.card I :=
      hcutsNodup.length_le_card
    simpa using hle.trans hcardJ
  have hvalid' : ∀ cut ∈ cuts,
      cut.entry ∈ extremePoints ℝ (Hpoly a b) ∧
      ⟪a cut.label.1, cut.entry⟫ = b cut.label.1 ∧
      cut.exit ∈ extremePoints ℝ (Hpoly a b) ∧
      ⟪a cut.label.1, cut.exit⟫ = b cut.label.1 := by
    intro cut hcut
    have hh := hvalid cut hcut
    rw [hrecover] at hh
    exact hh
  refine ⟨cuts, hcutsNodup, hlen, hvalid', ?_⟩
  rw [hrecover] at hr
  simpa [cuts, C] using hr

#print axioms target_slack_batch_reinsertion_with_pair_specific_cut_legs

end HirschTargetDeletion
