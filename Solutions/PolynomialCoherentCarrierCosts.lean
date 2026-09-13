import Solutions.PolynomialSignedCarrierAggregation

/-!
# Cubic direct-carrier costs use the already verified aggregate dimension mass

The companion paper gives 256*h^3 for the directed-cactus regime Gamma<=2,
using an explicit cone certificate and a CLASSICAL analytic diameter theorem.
This module does not assert that that external theorem is already formalized.
Actual selected-pair routes and their cost evidence remain explicit.
NEW UNCOMPILED candidates; no new platform verdict is asserted.
-/
open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschPolynomialAccess HirschRegionRoute HirschCircuitLocalization
open HirschSignedAggregate
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HirschRadial
variable {d n D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Generic cubic-rate composition, avoiding another hard-coded local model
in the deferred certificate. Every actual portal occurrence remains charged. -/
theorem DeferredClipCertificate.route_of_general_cubic_costs
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) (hinj : Function.Injective row)
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i,⟪a (row i),o⟫<b (row i))
    (hall : Fintype.card ι=n-d)
    (cost : ι → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℕ)
    (hroute : ∀ leg∈clipRepairCutLegs c.legs,
      Route (Adj (Hpoly a b)) (cost leg.label leg.entry leg.exit) leg.entry leg.exit)
    (K H : ℕ)
    (hcost : ∀ leg∈clipRepairCutLegs c.legs,
      cost leg.label leg.entry leg.exit≤K*(commonFaceDim a b leg.entry leg.exit)^3)
    (hH : ∀ leg∈clipRepairCutLegs c.legs,commonFaceDim a b leg.entry leg.exit≤H) :
    Route (Adj (Hpoly a b)) (D+3*K*H^2*(n-d)) u v := by
  have hm := (c.carrier_size_mass_le a b row hinj hbd o hstrict 0 (by omega)).1
  have hm' : ((clipRepairCutLegs c.legs).map fun leg =>
      commonFaceDim a b leg.entry leg.exit).sum≤3*(n-d) := by simpa [hall] using hm
  have hs := sum_cubic_cost_le_dimension_mass (clipRepairCutLegs c.legs)
    (fun leg => cost leg.label leg.entry leg.exit)
    (fun leg => commonFaceDim a b leg.entry leg.exit) K H hcost hH
  have hb : ((clipRepairCutLegs c.legs).map fun leg =>
      cost leg.label leg.entry leg.exit).sum≤3*K*H^2*(n-d) := by
    have h := hs.trans (Nat.mul_le_mul_left (K*H^2) hm')
    nlinarith
  obtain ⟨w,hw0,hwL,hstep⟩ := c.assemble cost hroute
  exact HirschProduct.pad_walk _ (Nat.add_le_add_left hb D) w hw0 hwL hstep

/-- The coherent-cycle local rate gives D+768*H^2*e. This finite arithmetic
identity is separate from the missing model-to-route formalization. -/
theorem coherent_cubic_coefficient (H e : ℕ) : 3*256*H^2*e=768*H^2*e := by ring

#print axioms DeferredClipCertificate.route_of_general_cubic_costs
#print axioms coherent_cubic_coefficient
end HirschRadial
