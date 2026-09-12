import Solutions.PolynomialGeodesicMassRouting
import Solutions.PolynomialTargetConeBatchReinsertion

/-!
# Keep only a target-tight basis; use an interior clipping center

Keeping ALL rows tight at a nonsimple target loses available-row budget.
A target-tight spanning selection already gives a pointed cone with the target
as its unique vertex. In particular, a d-row basis leaves exactly n-d cuts.
The additional cuts may be tight at the target; the clipping center is a supplied
strictly feasible interior point, NOT that target. This distinction is essential.

New candidate sources; no new local compiler/platform verdict is asserted.
-/
open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRegionRoute HirschRadial HirschCircuitLocalization HirschPolynomialAccess
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
namespace HirschTargetDeletion

/-- All rows are tight at v, and their map is injective. No assertion that
these are ALL active rows of a larger parent is necessary. -/
theorem tight_outer_unique_vertex_of_injective
    {d m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (htight : ∀ i, ⟪a i, v⟫ = b i) :
    extremePoints ℝ (Hpoly a b) = {v} := by
  have hv : v ∈ extremePoints ℝ (Hpoly a b) := by
    refine ⟨fun i => (htight i).le, ?_⟩
    intro p hp q hq hseg
    obtain ⟨α, β, hα, hβ, hsum, hcomb⟩ := hseg
    apply hinj
    funext i
    change ⟪a i, p⟫ = ⟪a i, v⟫
    rw [htight i]
    have heval := congrArg (fun z : EuclideanSpace ℝ (Fin d) => ⟪a i, z⟫) hcomb
    simp only [inner_add_right, inner_smul_right, htight i] at heval
    have hp' := hp i
    have hq' := hq i
    by_contra hn
    have hlt : ⟪a i, p⟫ < b i := lt_of_le_of_ne hp' hn
    have h₁ := mul_lt_mul_of_pos_left hlt hα
    have h₂ := mul_le_mul_of_nonneg_left hq' hβ.le
    have hb : α*b i + β*b i = b i := by rw [← add_mul, hsum, one_mul]
    linarith
  ext z
  constructor
  · intro hz
    apply Set.mem_singleton_iff.mpr
    apply sub_eq_zero.mp
    apply vertex_tight_rows_span_checked d m a b z hz (z-v)
    intro i hi
    rw [inner_sub_right, hi, htight i, sub_self]
  · intro hz
    have h : z=v := Set.mem_singleton_iff.mp hz
    simpa [h] using hv

/-- Generalized compact star cap: spanning tight rows suffice. -/
theorem compact_star_cap_of_spanning_tight_selection
    {d n m : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hbd : Bornology.IsBounded (Hpoly a b)) (e : Fin m → Fin n)
    (hinj : Function.Injective (HirschCircuit.rowMap (fun k => a (e k))))
    (htight : ∀ k, ⟪a (e k), v⟫ = b (e k)) :
    ∃ M : ℝ,
      let Q := HirschPointed.injectiveCappedHpoly
        (fun k => a (e k)) (fun k => b (e k)) M
      IsCompact Q ∧ Convex ℝ Q ∧ Hpoly a b ⊆ Q ∧
      v ∈ extremePoints ℝ Q ∧
      (∀ z ∈ extremePoints ℝ Q, z = v ∨ Adj Q v z) := by
  classical
  let ao := fun k => a (e k)
  let bo := fun k => b (e k)
  let c := HirschPointed.injectiveCapNormal ao
  have hverts : extremePoints ℝ (Hpoly ao bo) = {v} :=
    tight_outer_unique_vertex_of_injective ao bo v hinj htight
  have hPc : IsCompact (Hpoly a b) :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨HirschCapVertices.hpoly_isClosed a b, hbd⟩
  obtain ⟨M, hPbelow, _⟩ := HirschCapVertices.exists_level_above_compact_and_outer_vertices
    ao bo (Hpoly a b) hPc ⟨v, hv.1⟩ c
  let Q := HirschPointed.injectiveCappedHpoly ao bo M
  have hmodel : Q = Hpoly ao bo ∩ {z | ⟪c, z⟫ ≤ M} :=
    HirschPointed.injectiveCappedHpoly_eq_inter ao bo M
  have hQc : IsCompact Q := by
    apply Metric.isCompact_iff_isClosed_bounded.mpr
    refine ⟨?_, HirschPointed.injectiveCappedHpoly_isBounded ao bo M hinj⟩
    rw [hmodel]
    exact (HirschCapVertices.hpoly_isClosed ao bo).inter
      (isClosed_le (by fun_prop) continuous_const)
  have hQ : Convex ℝ Q := by
    rw [hmodel, ← HirschCapVertices.hpoly_cons_eq_inter]
    exact HirschCapVertices.hpoly_convex _ _
  have hcontain : Hpoly a b ⊆ Q := by
    intro z hz
    refine ⟨fun k => hz (e k), ?_⟩
    change HirschPointed.injectiveCapValue ao z ≤ M
    rw [← HirschPointed.injectiveCapNormal_eval]
    exact (hPbelow z hz).le
  have hvOuter : v ∈ extremePoints ℝ (Hpoly ao bo) := by rw [hverts]; exact Set.mem_singleton v
  have hvQ : v ∈ extremePoints ℝ Q := by
    rw [hmodel]
    exact HirschCapVertices.old_vertex_survives_cap (Hpoly ao bo) c M v hvOuter (hPbelow v hv.1).le
  have hstar := compact_cap_star_of_unique_vertex ao bo c M v
    (by rwa [← hmodel]) hverts
  rw [← hmodel] at hstar
  exact ⟨M, hQc, hQ, hcontain, hvQ, hstar⟩

/-- The complement of a supplied independent d-row target basis. -/
def basisRemainingRows {d n : ℕ} (e : Fin d ↪ Fin n) : Finset (Fin n) :=
  Finset.univ \ Finset.univ.map e

lemma basisRemainingRows_card {d n : ℕ} (e : Fin d ↪ Fin n) :
    (basisRemainingRows e).card = n-d := by
  classical
  have hc := Finset.card_sdiff_add_card_eq_card
    (show Finset.univ.map e ⊆ (Finset.univ : Finset (Fin n)) by simp)
  have hmap : (Finset.univ.map e).card = d := by simp
  change (basisRemainingRows e).card + (Finset.univ.map e).card = _ at hc
  simp only [hmap, Finset.card_univ, Fintype.card_fin] at hc
  omega

/-- Exactly n-d available cuts and D=1, even when the target is nonsimple.
No local route premise is needed to obtain the certificate. -/
theorem basis_star_deferred_clip_certificate
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (e : Fin d ↪ Fin n)
    (hinj : Function.Injective (HirschCircuit.rowMap (fun k => a (e k))))
    (htight : ∀ k, ⟪a (e k), v⟫ = b (e k))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i, ⟪a i, o⟫ < b i)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ extremePoints ℝ (Hpoly a b)) :
    Nonempty (DeferredClipCertificate (Hpoly a b)
      (fun i : basisRemainingRows e => a i.1)
      (fun i : basisRemainingRows e => b i.1) 1 v u) := by
  classical
  obtain ⟨M, hQc, hQ, hcontain, hvQ, hstar⟩ :=
    compact_star_cap_of_spanning_tight_selection a b v hv hbd e hinj htight
  let Q := HirschPointed.injectiveCappedHpoly (fun k => a (e k)) (fun k => b (e k)) M
  let aj := fun i : basisRemainingRows e => a i.1
  let bj := fun i : basisRemainingRows e => b i.1
  have hrecover : clipSet Q aj bj = Hpoly a b := by
    ext z
    constructor
    · rintro ⟨hzQ, hcuts⟩ i
      by_cases hi : i ∈ basisRemainingRows e
      · exact hcuts ⟨i, hi⟩
      · have him : i ∈ Finset.univ.map e := by
          simpa [basisRemainingRows] using hi
        obtain ⟨k, _, hk⟩ := Finset.mem_map.mp him
        have h := hzQ.1 k
        simpa only [hk] using h
    · intro hz
      exact ⟨hcontain hz, fun i => hz i.1⟩
  have hoQ : o ∈ Q := hcontain (fun i => (hstrict i).le)
  have hs : ∀ i : basisRemainingRows e, ⟪aj i, o⟫ < bj i := fun i => hstrict i.1
  have hvP : v ∈ extremePoints ℝ (clipSet Q aj bj) := by simpa [hrecover] using hv
  have huP : u ∈ extremePoints ℝ (clipSet Q aj bj) := by simpa [hrecover] using hu
  obtain ⟨y, hy, huy⟩ := HirschClipLift.endpoint_lift_to_outer_vertex Q hQc hQ aj bj u huP
  have hroute : Route (Adj Q) 1 v y := by
    apply route_one
    rcases hstar y hy with he | ha
    · exact Or.inl he.symm
    · exact Or.inr ha
  have hc := deferred_clip_certificate_of_lifted_endpoints Q hQc hQ aj bj 1
    o hoQ hs v u hvP huP v y hvQ hy (Or.inl rfl) huy hroute
  rwa [hrecover] at hc

/-- Full all-row mass bound with a target-tight basis and an interior center.
Every original row outside the basis is available, including other tight rows. -/
theorem basis_star_exists_linear_carrier_mass
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (e : Fin d ↪ Fin n)
    (hinj : Function.Injective (HirschCircuit.rowMap (fun k => a (e k))))
    (htight : ∀ k, ⟪a (e k), v⟫ = b (e k))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i, ⟪a i, o⟫ < b i)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ extremePoints ℝ (Hpoly a b)) :
    ∃ c : DeferredClipCertificate (Hpoly a b)
        (fun i : basisRemainingRows e => a i.1)
        (fun i : basisRemainingRows e => b i.1) 1 v u,
      ((clipRepairCutLegs c.legs).map fun leg =>
        commonFacePresentationExcess a b leg.entry leg.exit).sum ≤ 3*(n-d) := by
  classical
  obtain ⟨c⟩ := basis_star_deferred_clip_certificate a b v hv hbd e hinj htight o hstrict u hu
  refine ⟨c, ?_⟩
  have hc : Fintype.card (basisRemainingRows e) = n-d := by
    simpa only [Fintype.card_coe] using basisRemainingRows_card e
  have hm := c.carrier_mass_le a b Subtype.val Subtype.val_injective hbd o
    (fun i => hstrict i.1) 0 (by omega)
  simpa [hc] using hm

#print axioms tight_outer_unique_vertex_of_injective
#print axioms compact_star_cap_of_spanning_tight_selection
#print axioms basisRemainingRows_card
#print axioms basis_star_deferred_clip_certificate
#print axioms basis_star_exists_linear_carrier_mass
end HirschTargetDeletion
