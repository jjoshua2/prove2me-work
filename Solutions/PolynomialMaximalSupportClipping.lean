import Solutions.PolynomialDeferredClipping
import Solutions.PolynomialChordlessCarrierExcessTradeoff
import Solutions.PolynomialMinCarrierExcessRouting

/-! Maximum used cut support closes every local carrier call and gives an
actual ordinary-edge route with cost D + 3(n-d). -/
open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRegionRoute HirschCircuitLocalization HirschPolynomialAccess
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
namespace HirschRadial

variable {d n D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Recover a mixed leg from its projection to a cut leg. -/
theorem cut_leg_mem_iff {aj : ι → EuclideanSpace ℝ (Fin d)} {bj : ι → ℝ}
    {P : Set (EuclideanSpace ℝ (Fin d))} {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate P aj bj D u v)
    (leg : RegionLeg ι (EuclideanSpace ℝ (Fin d))) :
    leg ∈ clipRepairCutLegs c.legs ↔
      RegionLeg.mk (Sum.inl leg.label) leg.entry leg.exit ∈ c.legs := by
  constructor
  · intro h
    obtain ⟨mixed, hm, he⟩ := List.mem_filterMap.mp h
    rcases mixed with ⟨label, entry, exit⟩
    rcases label with i | rest
    · simp only at he
      injection he with he
      subst leg
      exact hm
    · simp at he
  · intro h
    exact List.mem_filterMap.mpr ⟨_, h, rfl⟩

/-- Used cut labels, independent of subsequent cost assignments. -/
def DeferredClipCertificate.cutSupport
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {aj : ι → EuclideanSpace ℝ (Fin d)} {bj : ι → ℝ}
    {u v : EuclideanSpace ℝ (Fin d)} (c : DeferredClipCertificate P aj bj D u v) :
    Finset ι := ((clipRepairCutLegs c.legs).map RegionLeg.label).toFinset

theorem DeferredClipCertificate.cutSupport_card
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {aj : ι → EuclideanSpace ℝ (Fin d)} {bj : ι → ℝ}
    {u v : EuclideanSpace ℝ (Fin d)} (c : DeferredClipCertificate P aj bj D u v) :
    c.cutSupport.card = (clipRepairCutLegs c.legs).length := by
  rw [DeferredClipCertificate.cutSupport,
    List.toFinset_card_of_nodup (clipRepairCutLeg_labels_nodup c.nodup), List.length_map]

/-- Maximum used support gives local excess at most three for each actual
charged portal pair. The ambient row map on cut labels is injective. -/
theorem DeferredClipCertificate.used_carrier_excess_le_three
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) (hinj : Function.Injective row)
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i, ⟪a (row i), o⟫ < b (row i))
    (hmax : c.cutSupport.card = n - d)
    (leg : RegionLeg ι (EuclideanSpace ℝ (Fin d)))
    (hleg : leg ∈ clipRepairCutLegs c.legs) :
    commonFacePresentationExcess a b leg.entry leg.exit ≤ 3 := by
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
  have hcnum : cuts.card = n - d := by
    rw [Finset.card_image_of_injective _ Sum.inl_injective]
    exact hmax
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
  exact commonFace_minExcess_le_three_of_chordless_maximal_rowFace_support
    a b F (Metric.isCompact_iff_isClosed_bounded.mpr ⟨hpoly_isClosed a b, hbd⟩)
    c.facesExtreme c.facesClosed rows c.path c.chordless cuts hcsub hrows hfaces hcnum
    (.inl leg.label) hi leg.entry leg.exit hp hq hbd hn hpi hqi

/-- The route closes whenever all actually selected carriers have excess at most
three, irrespective of how many cuts the chosen path uses. -/
theorem DeferredClipCertificate.route_of_used_carrier_excess_le_three
    (hsmall : SmallExcessHpolyBound)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n)
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (heasy : ∀ leg ∈ clipRepairCutLegs c.legs,
      commonFacePresentationExcess a b leg.entry leg.exit ≤ 3) :
    Route (Adj (Hpoly a b)) (D + 3 * c.cutSupport.card) u v := by
  have hlocal : ∀ leg ∈ clipRepairCutLegs c.legs,
      Route (Adj (Hpoly a b)) 3 leg.entry leg.exit := by
    intro leg hleg
    have he := heasy leg hleg
    have hmin : commonFaceMinSubpresentationCount a b leg.entry leg.exit ≤
        commonFaceDim a b leg.entry leg.exit + 3 := by
      unfold commonFacePresentationExcess at he
      omega
    have hdiam := commonFace_diamLE_three_of_minCount_le_dim_add_three
      hsmall a b leg.entry leg.exit hbd hmin
    have hf := c.fits _ ((cut_leg_mem_iff c leg).mp hleg)
    exact extreme_face_region (Hpoly a b) (commonFace a b leg.entry leg.exit) 3
      (commonFace_isExtreme a b leg.entry leg.exit) hdiam
      leg.entry ⟨hf.1.1, commonFace_u_mem a b _ _ hf.1.1.1⟩
      leg.exit ⟨hf.2.1.1, commonFace_x_mem a b _ _ hf.2.1.1.1⟩
  have hr := c.assemble (fun _ _ _ => 3) hlocal
  rw [c.cutSupport_card]
  simpa [Nat.mul_comm] using hr

/-- An end-to-end graph route in the maximum-support regime. No local route
hypothesis remains: the selected geometry discharges every local call using
the already-Proved small-excess theorem, supplied explicitly as hsmall. -/
theorem DeferredClipCertificate.route_of_maximal_support
    (hsmall : SmallExcessHpolyBound)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) (hinj : Function.Injective row)
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i, ⟪a (row i), o⟫ < b (row i))
    (hmax : c.cutSupport.card = n - d) :
    Route (Adj (Hpoly a b)) (D + 3 * (n - d)) u v := by
  have hroute := c.route_of_used_carrier_excess_le_three hsmall a b row hbd
    (fun leg hleg => c.used_carrier_excess_le_three a b row hinj hbd o hstrict hmax leg hleg)
  simpa [hmax] using hroute

#print axioms DeferredClipCertificate.used_carrier_excess_le_three
#print axioms DeferredClipCertificate.route_of_used_carrier_excess_le_three
#print axioms DeferredClipCertificate.route_of_maximal_support
end HirschRadial
