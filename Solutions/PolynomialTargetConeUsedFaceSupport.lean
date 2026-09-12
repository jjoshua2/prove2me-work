import Mathlib
import Solutions.PolynomialTargetConeBatchReinsertion
import Solutions.PolynomialTargetSlackUniformBudget
import Solutions.PolynomialSimultaneousClipUsedRegions

/-!
# Target-cone reinsertion with exact used-face support

The target-tight outer has a compact star cap, so pairwise outer routes cost two
and target-rooted outer routes cost one.  Restoring all target-slack cuts with
the path-sensitive simultaneous-clipping theorem exposes only the distinct
final cut faces actually used by each repair.

Because those cut labels are the subtype of rows strictly slack at the fixed
target vertex, their list length is at most the ambient row excess `n-d`.
The theorem does **not** bound the sum of the face-route budgets themselves;
that weighted amortization is still the active Polynomial Hirsch frontier.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRegionRoute

set_option autoImplicit false
set_option maxHeartbeats 7000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschTargetDeletion

/-- Restore all target-slack rows from the compact target-tight star while
exposing exactly the distinct final cut faces used by each repaired route.

Pairwise routes pay two outer-star edges plus the budgets on their used faces;
target-rooted routes pay one outer-star edge plus the budgets on their used
faces.  In both cases the used-face list is duplicate-free and has length at
most `n-d`. -/
theorem target_slack_batch_reinsertion_with_used_parent_faces
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
      ∀ w ∈ extremePoints ℝ (Hpoly a b),
        ∃ cuts : List J,
          cuts.Nodup ∧ cuts.length ≤ n - d ∧
          Route (Adj (Hpoly a b))
            (2 + (cuts.map (fun i : J => B i.1)).sum) u w) ∧
    (∀ u ∈ extremePoints ℝ (Hpoly a b),
        ∃ cuts : List J,
          cuts.Nodup ∧ cuts.length ≤ n - d ∧
          Route (Adj (Hpoly a b))
            (1 + (cuts.map (fun i : J => B i.1)).sum) v u) := by
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
  have hcutsLength : ∀ {cuts : List J}, cuts.Nodup → cuts.length ≤ n - d := by
    intro cuts hnd
    have hlen : cuts.length ≤ J.card := by
      simpa using hnd.length_le_card
    exact hlen.trans hJcard
  constructor
  · intro u hu w hw
    have hu' : u ∈ extremePoints ℝ (HirschRadial.clipSet Q aj bj) := by
      rw [hrecover]
      exact hu
    have hw' : w ∈ extremePoints ℝ (HirschRadial.clipSet Q aj bj) := by
      rw [hrecover]
      exact hw
    obtain ⟨cuts, hnd, hr⟩ :=
      HirschRadial.route_clip_with_parent_routes_used_cut_faces
        Q hQc hQ aj bj 2 Bj hdiam hFaces' v hvQ.1 hstrict u w hu' hw'
    refine ⟨cuts, hnd, hcutsLength hnd, ?_⟩
    simpa only [hrecover, Bj] using hr
  · intro u hu
    have hu' : u ∈ extremePoints ℝ (HirschRadial.clipSet Q aj bj) := by
      rw [hrecover]
      exact hu
    obtain ⟨cuts, hnd, hr⟩ :=
      HirschRadial.route_clip_from_root_with_parent_routes_used_cut_faces
        Q hQc hQ aj bj 1 Bj hFaces' v hvQ hvP hstrict hroot u hu'
    refine ⟨cuts, hnd, hcutsLength hnd, ?_⟩
    simpa only [hrecover, Bj] using hr

#print axioms target_slack_batch_reinsertion_with_used_parent_faces

end HirschTargetDeletion
