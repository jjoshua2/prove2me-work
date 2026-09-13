import Solutions.PolynomialGeodesicMassRouting

/-!
# Actual-pair intrinsic network costs use the global carrier-mass budget

The graph-theoretic target-insertion algorithm proves L<=h*M. The independent
finite certificate checker reconstructs h,M from the actual H-face. This file
proves the finite counting core and the same-pair budget consequence; it does
NOT pretend that the entire network algorithm is formalized by its interface.

New proof candidates; separate local Lean/axiom gate required.
-/
open Set Hirsch HirschRegionRoute HirschCircuitLocalization HirschPolynomialAccess
open scoped BigOperators RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace HirschNetwork

/-- Each positive pivot receives a phase and a deleted original-row label.
No phase may delete a row twice. Stationary basis exchanges are not paid edges. -/
theorem edge_count_of_distinct_phase_row_labels
    (L h M : ℕ) (stamp : Fin L → Fin h × Fin M)
    (hinj : Function.Injective stamp) : L≤h*M := by
  have h := Fintype.card_le_of_injective stamp hinj
  simpa using h

/-- Same estimate with actual intrinsic dimensions and row counts. -/
theorem sum_network_cost_le_mass
    {α : Type*} (ls : List α) (cost dim rows : α → ℕ) (H : ℕ)
    (hc : ∀ x∈ls,cost x≤dim x*rows x)
    (hd : ∀ x∈ls,dim x≤H) :
    (ls.map cost).sum≤H*(ls.map rows).sum := by
  induction ls with
  | nil => simp
  | cons x xs ih =>
    have hx := (hc x (by simp)).trans (Nat.mul_le_mul_right (rows x) (hd x (by simp)))
    have ht := ih (fun y hy => hc y (by simp [hy])) (fun y hy => hd y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,Nat.mul_add]
    omega
end HirschNetwork

namespace HirschRadial
open HirschNetwork
variable {d n D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The route premise is only for already selected actual vertex pairs.
Network forest certificates plus an exact intrinsic coordinate model discharge
it; no route for unused pairs or a uniform high-dimensional diameter is assumed. -/
theorem DeferredClipCertificate.route_of_intrinsic_network_costs
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
      Route (Adj (commonFace a b leg.entry leg.exit))
        (cost leg.label leg.entry leg.exit) leg.entry leg.exit)
    (hcost : ∀ leg∈clipRepairCutLegs c.legs,
      cost leg.label leg.entry leg.exit≤commonFaceDim a b leg.entry leg.exit*
        commonFaceMinSubpresentationCount a b leg.entry leg.exit)
    (H : ℕ) (hH : ∀ leg∈clipRepairCutLegs c.legs,commonFaceDim a b leg.entry leg.exit≤H) :
    Route (Adj (Hpoly a b)) (D+6*H*(n-d)) u v := by
  have hlocal : ∀ leg∈clipRepairCutLegs c.legs,
      Route (Adj (Hpoly a b)) (cost leg.label leg.entry leg.exit) leg.entry leg.exit := by
    intro leg hleg
    obtain ⟨w,hw0,hwL,hs⟩ := hroute leg hleg
    refine ⟨w,hw0,hwL,?_⟩
    intro j hj
    rcases hs j hj with he | ha
    · exact Or.inl he
    · exact Or.inr (commonFace_adj_to_parent a b leg.entry leg.exit ha)
  have hm := (c.carrier_size_mass_le a b row hinj hbd o hstrict 0 (by omega)).2
  have hm' : ((clipRepairCutLegs c.legs).map fun leg =>
      commonFaceMinSubpresentationCount a b leg.entry leg.exit).sum≤6*(n-d) := by
    simpa [hall,Nat.mul_assoc] using hm
  have hs := sum_network_cost_le_mass (clipRepairCutLegs c.legs)
    (fun leg => cost leg.label leg.entry leg.exit)
    (fun leg => commonFaceDim a b leg.entry leg.exit)
    (fun leg => commonFaceMinSubpresentationCount a b leg.entry leg.exit) H hcost hH
  have hc : ((clipRepairCutLegs c.legs).map fun leg => cost leg.label leg.entry leg.exit).sum≤6*H*(n-d) := by
    have h := hs.trans (Nat.mul_le_mul_left H hm')
    nlinarith
  obtain ⟨w,hw0,hwL,hs⟩ := c.assemble cost hlocal
  exact HirschProduct.pad_walk _ (Nat.add_le_add_left hc D) w hw0 hwL hs

#print axioms HirschNetwork.edge_count_of_distinct_phase_row_labels
#print axioms HirschNetwork.sum_network_cost_le_mass
#print axioms DeferredClipCertificate.route_of_intrinsic_network_costs
end HirschRadial
