import Solutions.PolynomialTargetAnchoredDeletion
import Solutions.PolynomialInjectiveHpolyVertexExistence
import Solutions.PolynomialSimultaneousClipParentRoutes

/-!
A target-tight outer has a unique old vertex. A compact cap of that outer is a
star about the surviving target, so its actual edge diameter is at most two.
Restoring ALL target-slack inequalities simultaneously charges each FINAL
cut-face parent-route budget only once. The target-rooted budget is one plus
the face sum; the pairwise diameter budget is two plus the same face sum.

No uniform bound on those face budgets or global polynomial recurrence is
asserted. In particular, this is not a proof of Polynomial Hirsch.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRegionRoute

set_option autoImplicit false
set_option maxHeartbeats 6000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschTargetDeletion

/-- Compact single-cap classification becomes a genuine star when the uncapped
outer has just one vertex. There is no auxiliary cap-chord relation here. -/
theorem compact_cap_star_of_unique_vertex
    {d m : ℕ}
    (a : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (M : ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hcompact : IsCompact (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ M}))
    (hverts : extremePoints ℝ (Hpoly a b) = {v}) :
    ∀ z ∈ extremePoints ℝ (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ M}),
      z = v ∨ Adj (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ M}) v z := by
  intro z hz
  rcases HirschCapVertices.compact_hpoly_cap_vertex_classification
      a b c M hcompact z hz with hold | hnew
  · left
    rw [hverts] at hold
    exact Set.mem_singleton_iff.mp hold
  · right
    obtain ⟨_hzcap, p, hp, _hpbelow, hpz⟩ := hnew
    rw [hverts] at hp
    have hpv : p = v := Set.mem_singleton_iff.mp hp
    simpa only [hpv] using hpz

/-- A star in the actual vertex/edge graph has padded diameter at most two. -/
theorem diamLE_two_of_vertex_star
    {d : ℕ} (Q : Set (EuclideanSpace ℝ (Fin d)))
    (v : EuclideanSpace ℝ (Fin d))
    (hstar : ∀ z ∈ extremePoints ℝ Q, z = v ∨ Adj Q v z) :
    DiamLE Q 2 := by
  intro x hx y hy
  have hleft : Route (Adj Q) 1 x v := by
    apply route_one
    rcases hstar x hx with heq | hadj
    · exact Or.inl heq
    · exact Or.inr ⟨hadj.1.symm, by simpa only [segment_symm] using hadj.2⟩
  have hright : Route (Adj Q) 1 v y := by
    apply route_one
    rcases hstar y hy with heq | hadj
    · exact Or.inl heq.symm
    · exact Or.inr hadj
  obtain ⟨p, hp0, hp1, hps⟩ := hleft
  obtain ⟨q, hq0, hq1, hqs⟩ := hright
  exact HirschProduct.append_walk (Adj Q) p q hp0 hp1 hq0 hq1 hps hqs

/-- The exact target-tight outer admits a compact, convex star cap containing
the entire bounded parent. The target survives as a vertex; all other capped
vertices are genuinely adjacent to it. No unknown outer graph cost remains. -/
theorem exists_compact_star_cap_of_target_tight_selection
    {d n m : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (e : Fin m → Fin n)
    (hcover : ∀ i, ⟪a i, v⟫ = b i → ∃ k, e k = i)
    (htight : ∀ k, ⟪a (e k), v⟫ = b (e k)) :
    ∃ M : ℝ,
      let Q := HirschPointed.injectiveCappedHpoly
        (fun k => a (e k)) (fun k => b (e k)) M
      IsCompact Q ∧ Convex ℝ Q ∧ Hpoly a b ⊆ Q ∧
      v ∈ extremePoints ℝ Q ∧
      (∀ z ∈ extremePoints ℝ Q, z = v ∨ Adj Q v z) ∧ DiamLE Q 2 := by
  classical
  let ao : Fin m → EuclideanSpace ℝ (Fin d) := fun k => a (e k)
  let bo : Fin m → ℝ := fun k => b (e k)
  let c := HirschPointed.injectiveCapNormal ao
  have hinj : Function.Injective (HirschCircuit.rowMap ao) :=
    selected_rowMap_injective_of_covers_target_tight a b v hv e hcover
  have hverts : extremePoints ℝ (Hpoly ao bo) = {v} :=
    selected_tight_outer_extremePoints_eq_singleton a b v hv e hcover htight
  have hPc : IsCompact (Hpoly a b) :=
    Metric.isCompact_iff_isClosed_bounded.2 ⟨HirschCapVertices.hpoly_isClosed a b, hbd⟩
  obtain ⟨M, hPbelow, _hOldBelow⟩ :=
    HirschCapVertices.exists_level_above_compact_and_outer_vertices
      ao bo (Hpoly a b) hPc ⟨v, hv.1⟩ c
  let Q := HirschPointed.injectiveCappedHpoly ao bo M
  have hmodel : Q = Hpoly ao bo ∩ {z | ⟪c, z⟫ ≤ M} :=
    HirschPointed.injectiveCappedHpoly_eq_inter ao bo M
  have hQclosed : IsClosed Q := by
    rw [hmodel]
    exact (HirschCapVertices.hpoly_isClosed ao bo).inter
      (isClosed_le (by fun_prop) continuous_const)
  have hQcompact : IsCompact Q :=
    Metric.isCompact_iff_isClosed_bounded.2
      ⟨hQclosed, HirschPointed.injectiveCappedHpoly_isBounded ao bo M hinj⟩
  have hQconvex : Convex ℝ Q := by
    rw [hmodel, ← HirschCapVertices.hpoly_cons_eq_inter]
    exact HirschCapVertices.hpoly_convex _ _
  have hcontain : Hpoly a b ⊆ Q := by
    intro z hz
    refine ⟨fun k => hz (e k), ?_⟩
    change HirschPointed.injectiveCapValue ao z ≤ M
    rw [← HirschPointed.injectiveCapNormal_eval]
    exact (hPbelow z hz).le
  have hvOuter : v ∈ extremePoints ℝ (Hpoly ao bo) := by
    rw [hverts]
    exact Set.mem_singleton v
  have hvQ : v ∈ extremePoints ℝ Q := by
    rw [hmodel]
    exact HirschCapVertices.old_vertex_survives_cap
      (Hpoly ao bo) c M v hvOuter (hPbelow v hv.1).le
  have hcompactModel : IsCompact (Hpoly ao bo ∩ {z | ⟪c, z⟫ ≤ M}) := by
    rw [← hmodel]
    exact hQcompact
  have hstar := compact_cap_star_of_unique_vertex ao bo c M v hcompactModel hverts
  rw [← hmodel] at hstar
  exact ⟨M, hQcompact, hQconvex, hcontain, hvQ, hstar, diamLE_two_of_vertex_star Q v hstar⟩

/-- Restore all target-slack rows as ONE simultaneous batch.

The original endpoints need not survive as vertices of the relaxed target
cone. Compact endpoint lifts and radial trace repair account for this.
Each final deleted-row face is charged once, even if the trace revisits it.
The supplied face routes are ordinary parent-edge routes and may leave the
face. Their costs are hypotheses, not automatically polynomial quantities.
-/
theorem target_slack_batch_reinsertion_with_parent_routes
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
    DiamLE (Hpoly a b) (2 + ∑ i : J, B i.1) ∧
    (∀ u ∈ extremePoints ℝ (Hpoly a b),
      Route (Adj (Hpoly a b)) (1 + ∑ i : J, B i.1) v u) := by
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
  have hFaces' : ∀ i : J, ∀ p ∈ extremePoints ℝ (HirschRadial.clipSet Q aj bj),
      ⟪aj i, p⟫ = bj i → ∀ q ∈ extremePoints ℝ (HirschRadial.clipSet Q aj bj),
      ⟪aj i, q⟫ = bj i → Route (Adj (HirschRadial.clipSet Q aj bj)) (Bj i) p q := by
    intro i p hp hpi q hq hqi
    rw [hrecover] at hp hq ⊢
    exact hFaces i.1 i.2 p hp hpi q hq hqi
  have hD := HirschRadial.diamLE_clip_of_strict_centre_with_parent_routes
    Q hQc hQ aj bj 2 Bj hdiam hFaces' v hvQ.1 hstrict
  have hroot : ∀ z ∈ extremePoints ℝ Q, Route (Adj Q) 1 v z := by
    intro z hz
    apply route_one
    rcases hstar z hz with heq | hedge
    · exact Or.inl heq.symm
    · exact Or.inr hedge
  have hvP : v ∈ extremePoints ℝ (HirschRadial.clipSet Q aj bj) := by
    rw [hrecover]
    exact hv
  have hR := HirschRadial.route_clip_from_root_with_parent_routes
    Q hQc hQ aj bj 1 Bj hFaces' v hvQ hvP hstrict hroot
  constructor
  · simpa only [hrecover] using hD
  · simpa only [hrecover] using hR

#print axioms compact_cap_star_of_unique_vertex
#print axioms diamLE_two_of_vertex_star
#print axioms exists_compact_star_cap_of_target_tight_selection
#print axioms target_slack_batch_reinsertion_with_parent_routes

end HirschTargetDeletion
