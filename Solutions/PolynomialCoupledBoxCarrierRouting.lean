import Solutions.PolynomialPositiveFeedbackBoxes
import Solutions.PolynomialPositivePerspective
import Solutions.PolynomialMaximalSupportClipping

/-! Positive-feedback carriers close actual deferred calls even when no
projective product split exists. All coordinate identities remain explicit. -/
open Set Hirsch HirschPairedBases HirschPositiveBoxes HirschPerspective
open HirschRegionRoute HirschPolynomialAccess HirschCircuitLocalization
open scoped BigOperators RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HirschPositiveBoxes

/-- Geometric model of a k-dimensional carrier, optionally in a positive
projective chart. There is no graph or diameter premise in this certificate. -/
structure PositiveBoxImage {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Set E) (k : ℕ) where
  C : Vec (Fin k) →ₗ[ℝ] Vec (Fin k)
  monotone : Monotone C
  b : Vec (Fin k)
  b_pos : ∀ i, 0<b i
  w : Vec (Fin k)
  w_pos : ∀ i, 0<w i
  weighted : ∀ i, C w i<w i
  chart : Vec (Fin k) →ₗ[ℝ] ℝ
  chart_pos : pairedPoly (LinearMap.id-C) b ⊆ positiveDomain chart
  embed : Vec (Fin k) →ᵃ[ℝ] E
  injective : Function.Injective embed
  image_eq : embed '' (perspective chart '' pairedPoly (LinearMap.id-C) b)=P

theorem PositiveBoxImage.diamLE {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {k : ℕ} (m : PositiveBoxImage P k) : DiamLE P k := by
  have hbase := positive_feedback_diamLE m.C m.monotone m.w m.w_pos m.weighted m.b m.b_pos
  have hchart := perspective_diamLE_image m.chart _ m.chart_pos k hbase
  have hembed := Hirsch.affineMap_diamLE_image_of_injective m.embed m.injective _ k hchart
  rwa [m.image_eq] at hembed

end HirschPositiveBoxes
namespace HirschRadial

/-- Charge exactly the intrinsic dimensions of certified actual vertex-pair
carriers. No route is requested for an unused pair or unused face. -/
theorem DeferredClipCertificate.route_of_used_positive_box_models
    {d n D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hmodels : ∀ leg ∈ clipRepairCutLegs c.legs,
      Nonempty (PositiveBoxImage (commonFace a b leg.entry leg.exit)
        (commonFaceDim a b leg.entry leg.exit))) :
    Route (Adj (Hpoly a b))
      (D+((clipRepairCutLegs c.legs).map fun leg =>
        commonFaceDim a b leg.entry leg.exit).sum) u v := by
  apply c.assemble (fun _ p q => commonFaceDim a b p q)
  intro leg hleg
  obtain ⟨m⟩ := hmodels leg hleg
  have hf := c.fits _ ((cut_leg_mem_iff c leg).mp hleg)
  exact extreme_face_region (Hpoly a b) (commonFace a b leg.entry leg.exit)
    (commonFaceDim a b leg.entry leg.exit)
    (commonFace_isExtreme a b leg.entry leg.exit) m.diamLE
    leg.entry ⟨hf.1.1,commonFace_u_mem a b _ _ hf.1.1.1⟩
    leg.exit ⟨hf.2.1.1,commonFace_x_mem a b _ _ hf.2.1.1.1⟩

/-- The additive dimension charge is at most d*r, independently of support
deficit or the number of recursive/projective separators. -/
theorem DeferredClipCertificate.route_of_used_positive_box_models_padded
    {d n D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hmodels : ∀ leg ∈ clipRepairCutLegs c.legs,
      Nonempty (PositiveBoxImage (commonFace a b leg.entry leg.exit)
        (commonFaceDim a b leg.entry leg.exit))) :
    Route (Adj (Hpoly a b)) (D+d*c.cutSupport.card) u v := by
  have hdim : ∀ p q : EuclideanSpace ℝ (Fin d), commonFaceDim a b p q≤d := by
    intro p q
    have h := Submodule.finrank_le (commonDirection a b p q)
    simpa [commonFaceDim] using h
  have hsum : ∀ ls : List (RegionLeg ι (EuclideanSpace ℝ (Fin d))),
      (ls.map fun leg => commonFaceDim a b leg.entry leg.exit).sum≤d*ls.length := by
    intro ls
    induction ls with
    | nil => simp
    | cons x xs ih =>
      have hx := hdim x.entry x.exit
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith
  have hcost := hsum (clipRepairCutLegs c.legs)
  rw [← c.cutSupport_card] at hcost
  obtain ⟨w,hw0,hwB,hs⟩ := c.route_of_used_positive_box_models a b row hmodels
  exact HirschProduct.pad_walk _ (Nat.add_le_add_left hcost D) w hw0 hwB hs

#print axioms HirschPositiveBoxes.PositiveBoxImage.diamLE
#print axioms DeferredClipCertificate.route_of_used_positive_box_models
#print axioms DeferredClipCertificate.route_of_used_positive_box_models_padded
end HirschRadial
