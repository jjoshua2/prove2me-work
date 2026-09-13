import Solutions.PolynomialGeodesicMassRouting

/-!
# Cubic signed-carrier route budgets on the SAME selected pairs

The external classical wide-normal-cone theorem plus the signed inverse bound
gives a mathematical local ordinary-edge bound 36*h^3. This module does NOT
import that theorem as an axiom or pretend its full geometric existence proof
is already formalized. It consumes actual local routes and their finite budgets,
and proves the exact same-certificate aggregate D+108*H^2*(n-d).
New uncompiled source; see the proof/verification boundary in the handoff.
-/
open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschPolynomialAccess HirschCircuitLocalization HirschRegionRoute
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HirschSignedAggregate

theorem sum_cubic_cost_le_dimension_mass {α : Type*}
    (ls : List α) (cost dim : α → ℕ) (K H : ℕ)
    (hcost : ∀ x ∈ ls, cost x ≤ K * dim x ^ 3)
    (hdim : ∀ x ∈ ls, dim x ≤ H) :
    (ls.map cost).sum ≤ K * H^2 * (ls.map dim).sum := by
  apply list_cost_sum_le_scaled_mass
  intro x hx
  have hc := hcost x hx
  have hd := hdim x hx
  have hs : dim x * dim x ≤ H * H := Nat.mul_le_mul hd hd
  have ht := Nat.mul_le_mul_right (dim x) hs
  have hm := Nat.mul_le_mul_left K ht
  calc
    cost x ≤ K * dim x ^ 3 := hc
    _ ≤ K * H^2 * dim x := by nlinarith

end HirschSignedAggregate
namespace HirschRadial
open HirschSignedAggregate
variable {d n D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Signed model recognition and local classical path existence remain outside
this statement. Every actual chosen local route is charged once per occurrence. -/
theorem DeferredClipCertificate.route_of_signed_cubic_costs
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) (hinj : Function.Injective row)
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i, ⟪a (row i),o⟫ < b (row i))
    (hall : Fintype.card ι = n-d)
    (cost : ι → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℕ)
    (hroute : ∀ leg ∈ clipRepairCutLegs c.legs,
      Route (Adj (Hpoly a b)) (cost leg.label leg.entry leg.exit) leg.entry leg.exit)
    (hcost : ∀ leg ∈ clipRepairCutLegs c.legs,
      cost leg.label leg.entry leg.exit ≤ 36 * (commonFaceDim a b leg.entry leg.exit)^3)
    (H : ℕ) (hH : ∀ leg ∈ clipRepairCutLegs c.legs,
      commonFaceDim a b leg.entry leg.exit ≤ H) :
    Route (Adj (Hpoly a b)) (D + 108 * H^2 * (n-d)) u v := by
  have hm := (c.carrier_size_mass_le a b row hinj hbd o hstrict 0 (by omega)).1
  have hm' : ((clipRepairCutLegs c.legs).map fun leg =>
      commonFaceDim a b leg.entry leg.exit).sum ≤ 3 * (n-d) := by simpa [hall] using hm
  have hs := sum_cubic_cost_le_dimension_mass (clipRepairCutLegs c.legs)
    (fun leg => cost leg.label leg.entry leg.exit)
    (fun leg => commonFaceDim a b leg.entry leg.exit) 36 H hcost hH
  have hb : ((clipRepairCutLegs c.legs).map fun leg =>
      cost leg.label leg.entry leg.exit).sum ≤ 108 * H^2 * (n-d) := by
    have h := hs.trans (Nat.mul_le_mul_left (36*H^2) hm')
    nlinarith
  obtain ⟨w,hw0,hwL,hstep⟩ := c.assemble cost hroute
  exact HirschProduct.pad_walk _ (Nat.add_le_add_left hb D) w hw0 hwL hstep

#print axioms HirschSignedAggregate.sum_cubic_cost_le_dimension_mass
#print axioms DeferredClipCertificate.route_of_signed_cubic_costs
end HirschRadial
