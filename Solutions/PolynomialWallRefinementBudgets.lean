import Solutions.PolynomialCoherentCarrierCosts

/-!
# Only the ADDED walls are charged in a normal-fan refinement

An affine objective segment meets a nonparallel comparison wall at most once.
A supplied L-edge base route has an objective itinerary with L+1 interpolation
segments and L base-edge corners. Its refined route budget is L+(L+1)*q.

The classical wide-fan three-segment construction, plus two within-base-cone
endpoint connectors, gives a separate local cost B+5q. The analytic theorem and
fan-refinement existence are NOT silently imported as axioms here. The final
adapter consumes actual routes with those finite budgets.
NEW UNCOMPILED source; the proof note states the full geometric scope.
-/
open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRegionRoute HirschCircuitLocalization HirschPolynomialAccess
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HirschWallRefinement

/-- An affine scalar cannot cross the same nonconstant wall twice. -/
theorem affine_wall_root_unique (a b s t : ℝ) (hne : a ≠ b)
    (hs : (1-s)*a+s*b=0) (ht : (1-t)*a+t*b=0) : s=t := by
  have h : (s-t)*(b-a)=0 := by nlinarith
  have hba : b-a≠0 := sub_ne_zero.mpr (Ne.symm hne)
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hba)

/-- Occurrence count, not distinct route vertices. A wall can be charged on
several segments, but at most once on each. -/
theorem events_of_injective_segment_wall_labels
    {α : Type*} [Fintype α] (segments walls : ℕ)
    (label : α → Fin segments × Fin walls) (hinj : Function.Injective label) :
    Fintype.card α ≤ segments*walls := by
  have h := Fintype.card_le_of_injective label hinj
  simpa using h

theorem route_lift_budget (L q added cost : ℕ)
    (hadded : added ≤ (L+1)*q) (hcost : cost ≤ L+added) :
    cost ≤ (q+1)*L+q := by nlinarith

/-- Five geometric segments suffice for the existential wide-core refinement
argument: two endpoint-fiber connectors and the classical three-piece path. -/
theorem five_segment_refinement_budget (base added q cost : ℕ)
    (hadded : added ≤ 5*q) (hcost : cost ≤ base+added) :
    cost ≤ base+5*q := by omega

/-- Keep the refinement charge additive across ACTUAL carrier occurrences. -/
theorem list_refined_cubic_cost
    {α : Type*} (ls : List α) (cost dim walls : α → ℕ) (K H : ℕ)
    (hc : ∀ x∈ls, cost x≤K*(dim x)^3+5*walls x)
    (hd : ∀ x∈ls, dim x≤H) :
    (ls.map cost).sum ≤ K*H^2*(ls.map dim).sum+5*(ls.map walls).sum := by
  induction ls with
  | nil => simp
  | cons x xs ih =>
    have hcost := hc x (by simp)
    have hdim := hd x (by simp)
    have hsquare := Nat.mul_le_mul hdim hdim
    have hcube := Nat.mul_le_mul_right (dim x) hsquare
    have hscaled := Nat.mul_le_mul_left K hcube
    have hx : cost x≤K*H^2*dim x+5*walls x := by nlinarith
    have ht := ih (fun y hy => hc y (by simp [hy]))
      (fun y hy => hd y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    omega

#print axioms affine_wall_root_unique
#print axioms events_of_injective_segment_wall_labels
#print axioms route_lift_budget
#print axioms five_segment_refinement_budget
#print axioms list_refined_cubic_cost
end HirschWallRefinement

namespace HirschRadial
open HirschWallRefinement
variable {d n D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Wide-core refinements contribute 5*sum(q_i), not a multiplier of the whole
base-routing cost. A uniform ordinary diameter bound alone does NOT imply the
local B+5q premise; the geometric wide-fan itinerary proof must supply it. -/
theorem DeferredClipCertificate.route_of_wall_refined_costs
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) (hinj : Function.Injective row)
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i,⟪a (row i),o⟫<b (row i))
    (hall : Fintype.card ι=n-d)
    (cost walls : ι → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℕ)
    (hroute : ∀ leg∈clipRepairCutLegs c.legs,
      Route (Adj (Hpoly a b)) (cost leg.label leg.entry leg.exit) leg.entry leg.exit)
    (K H : ℕ)
    (hc : ∀ leg∈clipRepairCutLegs c.legs,
      cost leg.label leg.entry leg.exit ≤ K*(commonFaceDim a b leg.entry leg.exit)^3+
        5*walls leg.label leg.entry leg.exit)
    (hH : ∀ leg∈clipRepairCutLegs c.legs,commonFaceDim a b leg.entry leg.exit≤H) :
    Route (Adj (Hpoly a b))
      (D+3*K*H^2*(n-d)+5*((clipRepairCutLegs c.legs).map fun leg =>
        walls leg.label leg.entry leg.exit).sum) u v := by
  have hm := (c.carrier_size_mass_le a b row hinj hbd o hstrict 0 (by omega)).1
  have hm' : ((clipRepairCutLegs c.legs).map fun leg =>
      commonFaceDim a b leg.entry leg.exit).sum≤3*(n-d) := by simpa [hall] using hm
  have hs := list_refined_cubic_cost (clipRepairCutLegs c.legs)
    (fun leg => cost leg.label leg.entry leg.exit)
    (fun leg => commonFaceDim a b leg.entry leg.exit)
    (fun leg => walls leg.label leg.entry leg.exit) K H hc hH
  have hb : ((clipRepairCutLegs c.legs).map fun leg => cost leg.label leg.entry leg.exit).sum ≤
      3*K*H^2*(n-d)+5*((clipRepairCutLegs c.legs).map fun leg =>
        walls leg.label leg.entry leg.exit).sum := by
    have h := Nat.mul_le_mul_left (K*H^2) hm'
    nlinarith
  obtain ⟨w,hw0,hwL,hstep⟩ := c.assemble cost hroute
  apply HirschProduct.pad_walk _ _ w hw0 hwL hstep
  omega

#print axioms DeferredClipCertificate.route_of_wall_refined_costs
end HirschRadial
