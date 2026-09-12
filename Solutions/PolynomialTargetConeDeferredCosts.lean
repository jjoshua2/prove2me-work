import Solutions.PolynomialTargetConePairPortalCosts
import Solutions.PolynomialLowDimensionalCarrierRouting

/-! Cost-independent target-cone certificates and the closed maximum-support regime. -/
open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRegionRoute HirschRadial HirschCircuitLocalization HirschPolynomialAccess
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
namespace HirschTargetDeletion

/-- The target-tight compact star gives pairwise and target-rooted certificates
before any local cut costs or routes are supplied. -/
theorem target_slack_deferred_clip_certificates
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (J : Finset (Fin n)) (hJ : ∀ i, i ∈ J ↔ ⟪a i, v⟫ < b i) :
    (∀ u ∈ extremePoints ℝ (Hpoly a b), ∀ w ∈ extremePoints ℝ (Hpoly a b),
      Nonempty (DeferredClipCertificate (Hpoly a b)
        (fun i : J => a i.1) (fun i : J => b i.1) 2 u w)) ∧
    (∀ u ∈ extremePoints ℝ (Hpoly a b),
      Nonempty (DeferredClipCertificate (Hpoly a b)
        (fun i : J => a i.1) (fun i : J => b i.1) 1 v u)) := by
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
  have hroot : ∀ z ∈ extremePoints ℝ Q, Route (Adj Q) 1 v z := by
    intro z hz
    apply route_one
    rcases hstar z hz with heq | hedge
    · exact Or.inl heq.symm
    · exact Or.inr hedge
  have hvP : v ∈ extremePoints ℝ (HirschRadial.clipSet Q aj bj) := by
    rw [hrecover]
    exact hv
  constructor
  · intro u hu w hw
    have hu' : u ∈ extremePoints ℝ (clipSet Q aj bj) := by simpa [hrecover] using hu
    have hw' : w ∈ extremePoints ℝ (clipSet Q aj bj) := by simpa [hrecover] using hw
    have hc := deferred_clip_certificate Q hQc hQ aj bj 2 hdiam v hvQ.1 hstrict
      u w hu' hw'
    rw [hrecover] at hc
    exact hc
  · intro u hu
    have hu' : u ∈ extremePoints ℝ (clipSet Q aj bj) := by simpa [hrecover] using hu
    obtain ⟨y, hy, huy⟩ := HirschClipLift.endpoint_lift_to_outer_vertex Q hQc hQ aj bj u hu'
    have hc := deferred_clip_certificate_of_lifted_endpoints
      Q hQc hQ aj bj 1 v hvQ.1 hstrict v u hvP hu'
      v y hvQ hy (Or.inl rfl) huy (hroot y hy)
    rw [hrecover] at hc
    exact hc

/-- Every vertex pair admits the deferred target-rooted certificate. If it uses
all n-d available excess units as distinct cuts, its local calls close and the
actual parent-edge route costs at most 1+3(n-d). -/
theorem target_slack_maximal_support_route
    (hsmall : SmallExcessHpolyBound)
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (J : Finset (Fin n)) (hJ : ∀ i, i ∈ J ↔ ⟪a i, v⟫ < b i)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ extremePoints ℝ (Hpoly a b)) :
    ∃ c : DeferredClipCertificate (Hpoly a b)
        (fun i : J => a i.1) (fun i : J => b i.1) 1 v u,
      c.cutSupport.card ≤ n-d ∧
      (c.cutSupport.card = n-d → Route (Adj (Hpoly a b)) (1 + 3 * (n-d)) v u) := by
  classical
  obtain ⟨c⟩ := (target_slack_deferred_clip_certificates a b v hv hbd J hJ).2 u hu
  have hfull : J = Finset.univ.filter (fun i => ⟪a i, v⟫ < b i) := by
    ext i
    simp [hJ i]
  have hJcard : J.card ≤ n-d := by
    rw [hfull]
    exact target_slack_rows_card_le_rowExcess a b v hv
  have hcard : c.cutSupport.card ≤ n-d :=
    (Finset.card_le_univ c.cutSupport).trans (by simpa using hJcard)
  refine ⟨c, hcard, ?_⟩
  intro hmax
  exact c.route_of_maximal_support hsmall a b Subtype.val Subtype.val_injective hbd v
    (fun i => (hJ i.1).mp i.2) hmax

/-- An explicit research frontier: either the target-rooted route is already
linear, or the same deferred certificate uses strictly fewer than n-d cuts and
contains an actual charged parent-vertex carrier of excess at least four.
The residual witness carries the cost-independent assembly callback. -/
theorem target_slack_linear_route_or_few_cut_high_excess_carrier
    (hsmall : SmallExcessHpolyBound)
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (J : Finset (Fin n)) (hJ : ∀ i, i ∈ J ↔ ⟪a i, v⟫ < b i)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ extremePoints ℝ (Hpoly a b)) :
    ∃ c : DeferredClipCertificate (Hpoly a b)
        (fun i : J => a i.1) (fun i : J => b i.1) 1 v u,
      c.cutSupport.card ≤ n-d ∧
      (Route (Adj (Hpoly a b)) (1 + 3 * (n-d)) v u ∨
        (0 < c.cutSupport.card ∧ c.cutSupport.card < n-d ∧
          ∃ leg ∈ clipRepairCutLegs c.legs,
            3 < commonFacePresentationExcess a b leg.entry leg.exit)) := by
  classical
  obtain ⟨c, hcard, _⟩ := target_slack_maximal_support_route hsmall a b v hv hbd J hJ u hu
  refine ⟨c, hcard, ?_⟩
  by_cases heasy : ∀ leg ∈ clipRepairCutLegs c.legs,
      commonFacePresentationExcess a b leg.entry leg.exit ≤ 3
  · left
    obtain ⟨w, hw0, hwB, hs⟩ :=
      c.route_of_used_carrier_excess_le_three hsmall a b Subtype.val hbd heasy
    exact HirschProduct.pad_walk (Adj (Hpoly a b)) (by omega) w hw0 hwB hs
  · right
    push Not at heasy
    obtain ⟨leg, hleg, hhard⟩ := heasy
    have hpos : 0 < c.cutSupport.card := Finset.card_pos.mpr
      ⟨leg.label, List.mem_toFinset.mpr (List.mem_map.mpr ⟨leg, hleg, rfl⟩)⟩
    have hnotmax : c.cutSupport.card ≠ n-d := by
      intro hmax
      have hsmallLeg := c.used_carrier_excess_le_three a b Subtype.val
        Subtype.val_injective hbd v (fun i => (hJ i.1).mp i.2) hmax leg hleg
      omega
    exact ⟨hpos, by omega, leg, hleg, hhard⟩

#print axioms target_slack_linear_route_or_few_cut_high_excess_carrier

/-- The unresolved selected carriers must have BOTH dimension at least six
and minimum-presentation excess at least four. Otherwise the target-rooted
ordinary-edge route has the displayed quadratic budget. The same certificate
still assembles any later routes for its actual cut pairs. -/
theorem target_slack_quadratic_route_or_few_cut_high_dim_high_excess_carrier
    (hsmall : SmallExcessHpolyBound) (hlar : LarmanHpolyBound)
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (J : Finset (Fin n)) (hJ : ∀ i, i ∈ J ↔ ⟪a i, v⟫ < b i)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ extremePoints ℝ (Hpoly a b)) :
    ∃ c : DeferredClipCertificate (Hpoly a b)
        (fun i : J => a i.1) (fun i : J => b i.1) 1 v u,
      c.cutSupport.card ≤ n-d ∧
      (Route (Adj (Hpoly a b)) (1 + (4*n+3) * (n-d)) v u ∨
        (0 < c.cutSupport.card ∧ c.cutSupport.card < n-d ∧
          ∃ leg ∈ clipRepairCutLegs c.legs,
            6 ≤ commonFaceDim a b leg.entry leg.exit ∧
            4 ≤ commonFacePresentationExcess a b leg.entry leg.exit)) := by
  classical
  obtain ⟨c, hcard, hr | ⟨hpos, hfew, _⟩⟩ :=
    target_slack_linear_route_or_few_cut_high_excess_carrier
      hsmall a b v hv hbd J hJ u hu
  · refine ⟨c, hcard, Or.inl ?_⟩
    obtain ⟨w, hw0, hwB, hs⟩ := hr
    have hmul := Nat.mul_le_mul_right (n-d) (show 3 ≤ 4*n+3 by omega)
    exact HirschProduct.pad_walk _ (by omega) w hw0 hwB hs
  · refine ⟨c, hcard, ?_⟩
    by_cases heasy : ∀ leg ∈ clipRepairCutLegs c.legs,
        commonFacePresentationExcess a b leg.entry leg.exit ≤ 3 ∨
          commonFaceDim a b leg.entry leg.exit ≤ 5
    · left
      obtain ⟨w, hw0, hwB, hs⟩ :=
        c.route_of_used_carriers_low_dimension_or_excess hsmall hlar a b Subtype.val hbd heasy
      have hmul := Nat.mul_le_mul_left (4*n+3) hcard
      exact HirschProduct.pad_walk _ (by omega) w hw0 hwB hs
    · right
      push Not at heasy
      obtain ⟨leg, hleg, he, hd⟩ := heasy
      exact ⟨hpos, hfew, leg, hleg, by omega, by omega⟩

#print axioms target_slack_quadratic_route_or_few_cut_high_dim_high_excess_carrier
#print axioms target_slack_deferred_clip_certificates
#print axioms target_slack_maximal_support_route
end HirschTargetDeletion
