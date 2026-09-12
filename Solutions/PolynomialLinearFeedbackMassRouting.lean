import Solutions.PolynomialAutomaticTargetBasis
import Solutions.PolynomialCoupledBoxCarrierRouting

/-! Combine actual feedback-carrier routes with all-available-row mass.
The cost is linear in excess even with unbounded dimension and support deficit.
The geometric feedback-model condition is retained explicitly. -/
open Set Hirsch HirschRegionRoute HirschRadial HirschPolynomialAccess
open HirschCircuitLocalization HirschPositiveBoxes HirschTargetDeletion
open scoped BigOperators RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace HirschRadial

/-- Exact dimension-cost feedback routes consume the joint dimension mass. -/
theorem DeferredClipCertificate.route_positive_boxes_of_all_row_mass
    {d n D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) (hinj : Function.Injective row)
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i, ⟪a (row i), o⟫ < b (row i))
    (defect : ℕ) (hdefect : Fintype.card ι + defect = n-d)
    (hmodels : ∀ leg ∈ clipRepairCutLegs c.legs,
      Nonempty (PositiveBoxImage (commonFace a b leg.entry leg.exit)
        (commonFaceDim a b leg.entry leg.exit))) :
    Route (Adj (Hpoly a b))
      (D + c.cutSupport.card * defect + 3 * Fintype.card ι) u v := by
  have hm := (c.carrier_size_mass_le a b row hinj hbd o hstrict defect hdefect).1
  obtain ⟨w, h0, hB, hs⟩ := c.route_of_used_positive_box_models a b row hmodels
  apply HirschProduct.pad_walk _ (by omega) w h0 hB hs

/-- A high-dimensional feedback image or an excess-at-most-three carrier.
Both alternatives are geometric; neither contains an assumed route. -/
def FeedbackOrSmallCarrier {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (p q : EuclideanSpace ℝ (Fin d)) : Prop :=
  Nonempty (PositiveBoxImage (commonFace a b p q) (commonFaceDim a b p q)) ∨
    commonFacePresentationExcess a b p q ≤ 3

/-- The two certified classes may be mixed on the same fixed repair.
At full availability the resulting cost is D+3(n-d). -/
theorem DeferredClipCertificate.route_mixed_feedback_small_of_all_row_mass
    (hsmall : SmallExcessHpolyBound)
    {d n D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) (hinj : Function.Injective row)
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i, ⟪a (row i), o⟫ < b (row i))
    (defect : ℕ) (hdefect : Fintype.card ι + defect = n-d)
    (heasy : ∀ leg ∈ clipRepairCutLegs c.legs,
      FeedbackOrSmallCarrier a b leg.entry leg.exit) :
    Route (Adj (Hpoly a b))
      (D + c.cutSupport.card * defect + 3 * Fintype.card ι) u v := by
  let cost := fun (_i : ι) (p q : EuclideanSpace ℝ (Fin d)) =>
    commonFacePresentationExcess a b p q
  have hlocal : ∀ leg ∈ clipRepairCutLegs c.legs,
      Route (Adj (Hpoly a b)) (cost leg.label leg.entry leg.exit) leg.entry leg.exit := by
    intro leg hleg
    have hf := c.fits _ ((cut_leg_mem_iff c leg).mp hleg)
    have hroute (K : ℕ) (hd : DiamLE (commonFace a b leg.entry leg.exit) K) :
        Route (Adj (Hpoly a b)) K leg.entry leg.exit :=
      extreme_face_region (Hpoly a b) (commonFace a b leg.entry leg.exit) K
        (commonFace_isExtreme a b leg.entry leg.exit) hd
        leg.entry ⟨hf.1.1, commonFace_u_mem a b _ _ hf.1.1.1⟩
        leg.exit ⟨hf.2.1.1, commonFace_x_mem a b _ _ hf.2.1.1.1⟩
    have he := heasy leg hleg
    change Nonempty (PositiveBoxImage (commonFace a b leg.entry leg.exit)
      (commonFaceDim a b leg.entry leg.exit)) ∨ _ at he
    rcases he with hm | hsmallExcess
    · obtain ⟨m⟩ := hm
      have hdim := commonFace_dim_le_minExcess_of_vertices a b leg.entry leg.exit
        hbd hf.1.1 hf.2.1.1
      obtain ⟨w, h0, hB, hs⟩ := hroute _ m.diamLE
      exact HirschProduct.pad_walk _ hdim w h0 hB hs
    · exact hroute _ (commonFace_diamLE_minPresentationExcess_of_le_three
        hsmall a b leg.entry leg.exit hbd hf.1.1.1 hsmallExcess)
  have hm := c.carrier_mass_le a b row hinj hbd o hstrict defect hdefect
  obtain ⟨w, h0, hB, hs⟩ := c.assemble cost hlocal
  exact HirschProduct.pad_walk _ (by dsimp only [cost]; omega) w h0 hB hs

end HirschRadial
namespace HirschTargetDeletion

/-- Choose a basis and actual portals before requesting models. If every charged
carrier is feedback or small-excess, that same certificate gives 1+3(n-d).
No basis, simplicity, dimension cap, or bound on used-support deficit is supplied. -/
theorem exists_automatic_basis_linear_mixed_route
    (hsmall : SmallExcessHpolyBound) {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i, ⟪a i, o⟫ < b i)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ extremePoints ℝ (Hpoly a b)) :
    ∃ e : Fin d ↪ Fin n,
      ∃ c : DeferredClipCertificate (Hpoly a b)
          (fun i : basisRemainingRows e => a i.1)
          (fun i : basisRemainingRows e => b i.1) 1 v u,
        ((clipRepairCutLegs c.legs).map fun leg =>
          commonFacePresentationExcess a b leg.entry leg.exit).sum ≤ 3*(n-d) ∧
        ((∀ leg ∈ clipRepairCutLegs c.legs,
            FeedbackOrSmallCarrier a b leg.entry leg.exit) →
          Route (Adj (Hpoly a b)) (1+3*(n-d)) v u) := by
  classical
  obtain ⟨e, c, hm⟩ := exists_automatic_basis_star_linear_mass a b v hv hbd o hstrict u hu
  refine ⟨e, c, hm, ?_⟩
  intro heasy
  have hc : Fintype.card (basisRemainingRows e) = n-d := by
    simpa only [Fintype.card_coe] using basisRemainingRows_card e
  have h := c.route_mixed_feedback_small_of_all_row_mass hsmall a b
    Subtype.val Subtype.val_injective hbd o (fun i => hstrict i.1)
    0 (by omega) heasy
  simpa [hc] using h

#print axioms HirschRadial.DeferredClipCertificate.route_positive_boxes_of_all_row_mass
#print axioms HirschRadial.DeferredClipCertificate.route_mixed_feedback_small_of_all_row_mass
#print axioms exists_automatic_basis_linear_mixed_route
end HirschTargetDeletion
