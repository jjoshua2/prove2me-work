import Solutions.PolynomialGeodesicRowIncidence
import Solutions.PolynomialMaximalSupportClipping
import Solutions.PolynomialVertexCarrierIntrinsicBudget

/-!
# Joint carrier excess charged to ALL available cuts

For the exact deferred clipping certificate, let s be the number of available
cut rows, r the number actually selected, and e=n-d. The new estimate is

    sum(actual carrier excesses) + r*s <= r*e + 3*s.

When s+a=e this becomes sum <= r*a+3*s; in particular s=e gives sum <=3*e
WITHOUT maximal selected support, low cut rank, or a product assumption.
This is a resource bound, NOT an edge-distance bound for high-excess carriers.

New source: separate pinned Lean compilation/axiom audit required.
-/
open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschPolynomialAccess HirschRegionRoute
set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section
namespace HirschCircuitLocalization

/-- Unselected row faces may also be disjoint from the actual current face.
Unlike the old selected-only lemma, available need not lie on the path. -/
theorem commonFace_available_contact_budget
    {d n : ℕ} {V : Type*} [DecidableEq V]
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : V → Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact (Hpoly a b)) (hbd : Bornology.IsBounded (Hpoly a b))
    (hF : ∀ i, IsExtreme ℝ (Hpoly a b) (F i))
    (hclosed : ∀ i, IsClosed (F i))
    (available : Finset V) (row : V → Fin n)
    (hinj : Set.InjOn row (↑available : Set V))
    (hfaces : ∀ i ∈ available, F i = hpolyRowFace a b (row i))
    (i : V) (hi : i ∈ available)
    (p q : EuclideanSpace ℝ (Fin d))
    (hp : p ∈ extremePoints ℝ (Hpoly a b))
    (hq : q ∈ extremePoints ℝ (Hpoly a b))
    (hai : a (row i) ≠ 0)
    (hpi : ⟪a (row i), p⟫ = b (row i))
    (hqi : ⟪a (row i), q⟫ = b (row i)) :
    commonFacePresentationExcess a b p q + available.card ≤
      (n-d) + availableContactLoad
        (intersectionGraph (fun k => extremePoints ℝ (Hpoly a b) ∩ F k)) available i := by
  classical
  let G := intersectionGraph (fun k => extremePoints ℝ (Hpoly a b) ∩ F k)
  let contacts := available.filter (fun j => ClosedNear G j i)
  let absent := available \ contacts
  let J := absent.image row
  have habsent : absent ⊆ available := Finset.sdiff_subset
  have hJcard : J.card = absent.card := by
    apply Finset.card_image_iff.mpr
    intro x hx y hy hxy
    exact hinj (habsent hx) (habsent hy) hxy
  have hdisjoint : ∀ j ∈ J,
      Disjoint (hpolyRowFace a b (row i)) (hpolyRowFace a b j) := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    have hkA := habsent hk
    have hnot : ¬ ClosedNear G k i := by
      intro hn
      exact (Finset.mem_sdiff.mp hk).2 (Finset.mem_filter.mpr ⟨hkA, hn⟩)
    have hik : i ≠ k := by intro h; exact hnot (Or.inl h.symm)
    have hnadj : ¬ G.Adj i k := by intro h; exact hnot (Or.inr h.symm)
    have hd := closed_extreme_faces_disjoint_of_region_nonadj
      (Hpoly a b) F hP hF hclosed hik hnadj
    simpa only [hfaces i hi, hfaces k hkA] using hd
  have hs := commonFace_minExcess_add_disjoint_rowFaces_le
    a b p q hp hq hbd (row i) hai hpi hqi J hdisjoint
  rw [hJcard] at hs
  have hpart : absent.card + contacts.card = available.card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  change commonFacePresentationExcess a b p q + available.card ≤ (n-d) + contacts.card
  unfold commonFacePresentationExcess
  omega
end HirschCircuitLocalization

namespace HirschRadial
open HirschCircuitLocalization
variable {d n D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- All available cut labels touching the selected current cut label, not
just the cuts retained on the path. -/
def DeferredClipCertificate.allCutContactLoad
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {aj : ι → EuclideanSpace ℝ (Fin d)} {bj : ι → ℝ}
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate P aj bj D u v) (i : ι) : ℕ := by
  classical
  exact availableContactLoad
    (intersectionGraph (fun k => extremePoints ℝ P ∩
      clipRepairPathRegion (D := D) P aj bj c.trace u v k))
    (Finset.univ.image (Sum.inl : ι → Sum ι (Sum (Fin D) (Fin 2)))) (Sum.inl i)

/-- The actual clipping path has the required global metric minimality.
Every available row is charged by at most three selected cut labels. -/
theorem DeferredClipCertificate.allCutContactLoad_sum_le
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {aj : ι → EuclideanSpace ℝ (Fin d)} {bj : ι → ℝ}
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate P aj bj D u v) :
    ((clipRepairCutLegs c.legs).map fun leg => c.allCutContactLoad leg.label).sum ≤
      3 * Fintype.card ι := by
  classical
  let available := Finset.univ.image
    (Sum.inl : ι → Sum ι (Sum (Fin D) (Fin 2)))
  let labels := (clipRepairCutLegs c.legs).map
    (fun leg => (Sum.inl leg.label : Sum ι (Sum (Fin D) (Fin 2))))
  have hnd : labels.Nodup := by
    have h := (clipRepairCutLeg_labels_nodup c.nodup).map
      (Sum.inl_injective : Function.Injective (Sum.inl : ι → Sum ι (Sum (Fin D) (Fin 2))))
    simpa only [labels, List.map_map] using h
  have hsub : ∀ i ∈ labels, i ∈ c.path.support := by
    intro i hi
    obtain ⟨leg, hleg, rfl⟩ := List.mem_map.mp hi
    have hm := (cut_leg_mem_iff c leg).mp hleg
    have hl : Sum.inl leg.label ∈ c.legs.map RegionLeg.label :=
      List.mem_map.mpr ⟨_, hm, rfl⟩
    rwa [c.labels] at hl
  have hc : available.card = Fintype.card ι := by
    rw [Finset.card_image_of_injective _ Sum.inl_injective]
    simp
  have h := geodesic_list_available_load c.path c.shortest available labels hnd hsub
  rw [hc] at h
  simpa only [labels, List.map_map, DeferredClipCertificate.allCutContactLoad, available] using h

/-- Pointwise resource bound on the SAME actual charged vertex pair. -/
theorem DeferredClipCertificate.used_carrier_all_available_budget
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) (hinj : Function.Injective row)
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i, ⟪a (row i), o⟫ < b (row i))
    (leg : RegionLeg ι (EuclideanSpace ℝ (Fin d)))
    (hleg : leg ∈ clipRepairCutLegs c.legs) :
    commonFacePresentationExcess a b leg.entry leg.exit + Fintype.card ι ≤
      (n-d) + c.allCutContactLoad leg.label := by
  classical
  let F := clipRepairPathRegion (D := D) (Hpoly a b)
    (fun i => a (row i)) (fun i => b (row i)) c.trace u v
  let available := Finset.univ.image
    (Sum.inl : ι → Sum ι (Sum (Fin D) (Fin 2)))
  let rows : Sum ι (Sum (Fin D) (Fin 2)) → Fin n :=
    fun k => match k with | .inl j => row j | .inr _ => row leg.label
  have hrows : Set.InjOn rows (↑available : Set (Sum ι (Sum (Fin D) (Fin 2)))) := by
    intro x hx y hy he
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
    exact congrArg Sum.inl (hinj he)
  have hfaces : ∀ k ∈ available, F k = hpolyRowFace a b (rows k) := by
    intro k hk
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
    rfl
  have hi : Sum.inl leg.label ∈ available := Finset.mem_image.mpr
    ⟨leg.label, Finset.mem_univ _, rfl⟩
  have hf := c.fits _ ((cut_leg_mem_iff c leg).mp hleg)
  have hp : leg.entry ∈ extremePoints ℝ (Hpoly a b) := hf.1.1
  have hq : leg.exit ∈ extremePoints ℝ (Hpoly a b) := hf.2.1.1
  have hpi : ⟪a (row leg.label), leg.entry⟫ = b (row leg.label) := hf.1.2.2
  have hqi : ⟪a (row leg.label), leg.exit⟫ = b (row leg.label) := hf.2.1.2.2
  have hn := row_ne_zero_of_tight_and_strict a b (row leg.label) leg.entry o
    hpi (hstrict leg.label)
  have h := commonFace_available_contact_budget a b F
    (Metric.isCompact_iff_isClosed_bounded.mpr ⟨hpoly_isClosed a b, hbd⟩) hbd
    c.facesExtreme c.facesClosed available rows hrows hfaces (.inl leg.label) hi
    leg.entry leg.exit hp hq hn hpi hqi
  have hc : available.card = Fintype.card ι := by
    rw [Finset.card_image_of_injective _ Sum.inl_injective]
    simp
  rw [hc] at h
  exact h

/-- Main joint resource theorem. No cut-rank, maximal used support, simplicity,
 or low-dimensional-carrier premise is present. -/
theorem DeferredClipCertificate.carrier_mass_subtraction_free
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) (hinj : Function.Injective row)
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i, ⟪a (row i), o⟫ < b (row i)) :
    ((clipRepairCutLegs c.legs).map fun leg =>
      commonFacePresentationExcess a b leg.entry leg.exit).sum +
      c.cutSupport.card * Fintype.card ι ≤
        c.cutSupport.card * (n-d) + 3 * Fintype.card ι := by
  have hs := list_sum_available_budget (clipRepairCutLegs c.legs)
    (fun leg => commonFacePresentationExcess a b leg.entry leg.exit)
    (fun leg => c.allCutContactLoad leg.label) (Fintype.card ι) (n-d)
    (fun leg hleg => c.used_carrier_all_available_budget a b row hinj hbd o hstrict leg hleg)
  have hloads := c.allCutContactLoad_sum_le
  rw [c.cutSupport_card]
  omega

/-- a is the excess not represented among the available cut labels, NOT the
used-support deficit g=e-r. At a=0, the total mass is at most 3e for every r. -/
theorem DeferredClipCertificate.carrier_mass_le
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) (hinj : Function.Injective row)
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i, ⟪a (row i), o⟫ < b (row i))
    (defect : ℕ) (hdefect : Fintype.card ι + defect = n-d) :
    ((clipRepairCutLegs c.legs).map fun leg =>
      commonFacePresentationExcess a b leg.entry leg.exit).sum ≤
      c.cutSupport.card * defect + 3 * Fintype.card ι := by
  have h := c.carrier_mass_subtraction_free a b row hinj hbd o hstrict
  rw [← hdefect, Nat.mul_add] at h
  omega

#print axioms HirschCircuitLocalization.commonFace_available_contact_budget
#print axioms DeferredClipCertificate.allCutContactLoad_sum_le
#print axioms DeferredClipCertificate.used_carrier_all_available_budget
#print axioms DeferredClipCertificate.carrier_mass_subtraction_free
#print axioms DeferredClipCertificate.carrier_mass_le
end HirschRadial
