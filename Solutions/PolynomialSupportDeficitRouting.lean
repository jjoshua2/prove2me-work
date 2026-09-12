import Solutions.PolynomialVertexCarrierIntrinsicBudget
import Solutions.PolynomialTargetConeDeferredCosts

/-!
# Ordinary-edge routes parameterized by unused-cut deficit

On the same chosen certificate, write r + g = n-d. The existing chordless
tradeoff gives every actual cut carrier excess at most g+3. Vertex-pair
normalization makes its dimension at most g+3 and its minimum row count at
most 2(g+3). Intrinsic Larman then closes EVERY call, giving

  D + 2(g+3) * 2^g * r.

This is an actual edge-route bound, not merely a bound on excesses.
It is polynomial for fixed g, and when 2^g is polynomial in the input size.
No claim is made that g has a uniform logarithmic bound for arbitrary inputs.

This independent follow-up uses merged #193/#200, so it does not edit or block
another agent's verification of #201. Its sharper degrees can be substituted
in the cap K through the first module. New source is a compiler candidate.
-/
open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRegionRoute HirschCircuitLocalization HirschPolynomialAccess
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
namespace HirschRadial

variable {d n D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Generalize #200's maximum-support adapter to arbitrary nonnegative deficit.
The selected path, selected labels and actual portal pair never change. -/
theorem DeferredClipCertificate.used_carrier_excess_le_support_deficit_add_three
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) (hinj : Function.Injective row)
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i, ⟪a (row i), o⟫ < b (row i))
    (g : ℕ) (hgap : c.cutSupport.card + g = n-d)
    (leg : RegionLeg ι (EuclideanSpace ℝ (Fin d)))
    (hleg : leg ∈ clipRepairCutLegs c.legs) :
    commonFacePresentationExcess a b leg.entry leg.exit ≤ g+3 := by
  classical
  let F := clipRepairPathRegion (D := D) (Hpoly a b)
    (fun i => a (row i)) (fun i => b (row i)) c.trace u v
  let cuts := c.cutSupport.image (Sum.inl : ι → Sum ι (Sum (Fin D) (Fin 2)))
  let rows : Sum ι (Sum (Fin D) (Fin 2)) → Fin n :=
    fun k => match k with | .inl i => row i | .inr _ => row leg.label
  have hcsub : cuts ⊆ c.path.support.toFinset := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨l, hl, hli⟩ := List.mem_map.mp (List.mem_toFinset.mp hi)
    have hm := (cut_leg_mem_iff c l).mp hl
    have hlabel : Sum.inl l.label ∈ c.legs.map RegionLeg.label :=
      List.mem_map.mpr ⟨_, hm, rfl⟩
    rw [c.labels] at hlabel
    exact List.mem_toFinset.mpr (by simpa [hli] using hlabel)
  have hcnum : cuts.card = c.cutSupport.card :=
    Finset.card_image_of_injective _ Sum.inl_injective
  have hrows : Set.InjOn rows (↑cuts : Set (Sum ι (Sum (Fin D) (Fin 2)))) := by
    intro x hx y hy he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    exact congrArg Sum.inl (hinj he)
  have hfaces : ∀ k ∈ cuts, F k = hpolyRowFace a b (rows k) := by
    intro k hk
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
    rfl
  have hi : Sum.inl leg.label ∈ cuts :=
    Finset.mem_image.mpr ⟨leg.label, List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨leg, hleg, rfl⟩), rfl⟩
  have hfit := c.fits _ ((cut_leg_mem_iff c leg).mp hleg)
  have hp : leg.entry ∈ extremePoints ℝ (Hpoly a b) := hfit.1.1
  have hq : leg.exit ∈ extremePoints ℝ (Hpoly a b) := hfit.2.1.1
  have hpi : ⟪a (row leg.label), leg.entry⟫ = b (row leg.label) := hfit.1.2.2
  have hqi : ⟪a (row leg.label), leg.exit⟫ = b (row leg.label) := hfit.2.1.2.2
  have hn := row_ne_zero_of_tight_and_strict a b (row leg.label) leg.entry o
    hpi (hstrict leg.label)
  have htrade := commonFace_minExcess_add_selected_sub_three_le_of_chordless_rowFaces
    a b F (Metric.isCompact_iff_isClosed_bounded.mpr ⟨hpoly_isClosed a b, hbd⟩)
    c.facesExtreme c.facesClosed rows c.path c.chordless cuts hcsub hrows hfaces
    (.inl leg.label) hi leg.entry leg.exit hp hq hbd hn hpi hqi
  rw [hcnum] at htrade
  unfold commonFacePresentationExcess
  omega

/-- Convert an actual selected excess cap directly into a route, without any
recursive diameter premise or requirement concerning unused portal pairs. -/
theorem DeferredClipCertificate.route_of_used_carrier_excess_cap
    (hlar : LarmanHpolyBound)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (K : ℕ) (hcap : ∀ leg ∈ clipRepairCutLegs c.legs,
      commonFacePresentationExcess a b leg.entry leg.exit ≤ K) :
    Route (Adj (Hpoly a b)) (D + ((2*K) * 2^(K-3)) * c.cutSupport.card) u v := by
  have hlocal : ∀ leg ∈ clipRepairCutLegs c.legs,
      Route (Adj (Hpoly a b)) ((2*K) * 2^(K-3)) leg.entry leg.exit := by
    intro leg hleg
    have hf := c.fits _ ((cut_leg_mem_iff c leg).mp hleg)
    have hdiam := commonFace_diamLE_two_mul_cap_mul_pow
      hlar a b leg.entry leg.exit hbd hf.1.1 hf.2.1.1 K (hcap leg hleg)
    exact extreme_face_region (Hpoly a b) (commonFace a b leg.entry leg.exit)
      ((2*K) * 2^(K-3)) (commonFace_isExtreme a b leg.entry leg.exit) hdiam
      leg.entry ⟨hf.1.1, commonFace_u_mem a b _ _ hf.1.1.1⟩
      leg.exit ⟨hf.2.1.1, commonFace_x_mem a b _ _ hf.2.1.1.1⟩
  have hr := c.assemble (fun _ _ _ => (2*K) * 2^(K-3)) hlocal
  rw [c.cutSupport_card]
  simpa [Nat.mul_comm] using hr

/-- All selected calls close at fixed support deficit, including high excess
and high dimension. The dependence on the deficit is explicitly exponential. -/
theorem DeferredClipCertificate.route_of_support_deficit
    (hlar : LarmanHpolyBound)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) (hinj : Function.Injective row)
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i, ⟪a (row i), o⟫ < b (row i))
    (g : ℕ) (hgap : c.cutSupport.card + g = n-d) :
    Route (Adj (Hpoly a b)) (D + (2*(g+3) * 2^g) * c.cutSupport.card) u v := by
  have hr := c.route_of_used_carrier_excess_cap hlar a b row hbd (g+3)
    (fun leg hleg => c.used_carrier_excess_le_support_deficit_add_three
      a b row hinj hbd o hstrict g hgap leg hleg)
  simpa using hr

/-- In particular, every deficit-at-most-two certificate costs at most D+40r.
No matching, independence, factorization or further adjacency premise occurs. -/
theorem DeferredClipCertificate.route_of_support_deficit_le_two
    (hlar : LarmanHpolyBound)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) (hinj : Function.Injective row)
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i, ⟪a (row i), o⟫ < b (row i))
    (g : ℕ) (hgap : c.cutSupport.card + g = n-d) (hg : g ≤ 2) :
    Route (Adj (Hpoly a b)) (D + 40 * c.cutSupport.card) u v := by
  have hr := c.route_of_used_carrier_excess_cap hlar a b row hbd 5 (by
    intro leg hleg
    have hc := c.used_carrier_excess_le_support_deficit_add_three
      a b row hinj hbd o hstrict g hgap leg hleg
    omega)
  norm_num at hr ⊢
  exact hr

#print axioms DeferredClipCertificate.used_carrier_excess_le_support_deficit_add_three
#print axioms DeferredClipCertificate.route_of_used_carrier_excess_cap
#print axioms DeferredClipCertificate.route_of_support_deficit
#print axioms DeferredClipCertificate.route_of_support_deficit_le_two
end HirschRadial

namespace HirschTargetDeletion
open HirschRadial

/-- A fully assembled target-rooted edge route and the SAME certificate's
unused-cut deficit. The deficit is not asserted small for all polyhedra. -/
theorem target_slack_route_with_support_deficit_budget
    (hlar : LarmanHpolyBound) {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (J : Finset (Fin n)) (hJ : ∀ i, i ∈ J ↔ ⟪a i, v⟫ < b i)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ extremePoints ℝ (Hpoly a b)) :
    ∃ c : DeferredClipCertificate (Hpoly a b)
        (fun i : J => a i.1) (fun i : J => b i.1) 1 v u,
      ∃ g : ℕ, c.cutSupport.card + g = n-d ∧
        Route (Adj (Hpoly a b)) (1 + (2*(g+3) * 2^g) * c.cutSupport.card) v u := by
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
  let g := (n-d) - c.cutSupport.card
  have hgap : c.cutSupport.card + g = n-d := by dsimp [g]; omega
  refine ⟨c, g, hgap, ?_⟩
  exact c.route_of_support_deficit hlar a b Subtype.val Subtype.val_injective hbd v
    (fun i => (hJ i.1).mp i.2) g hgap

/-- Integer form of the logarithmic-deficit criterion, avoiding real logarithms.
For N>=1, r,g<=N and 2^g<=N^k imply a fixed-degree polynomial route budget.
This is an implication, not an assertion that arbitrary certificates satisfy it. -/
theorem support_deficit_budget_le_polynomial
    (D r g N k : ℕ) (hN : 1 ≤ N) (hr : r ≤ N) (hg : g ≤ N)
    (hpow : 2^g ≤ N^k) :
    D + (2*(g+3) * 2^g) * r ≤ D + 8 * N^(k+2) := by
  have hfactor : 2*(g+3) ≤ 8*N := by omega
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul hfactor hpow) hr
  have hid : ((8*N) * N^k) * N = 8 * N^(k+2) := by
    rw [pow_add]
    ring
  rw [hid] at hmul
  omega

#print axioms target_slack_route_with_support_deficit_budget
#print axioms support_deficit_budget_le_polynomial
end HirschTargetDeletion
