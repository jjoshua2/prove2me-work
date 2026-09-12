import Solutions.PolynomialAllCutCarrierMass

/-!
# Convert joint resource mass into selected-pair ordinary-edge bounds

Metric geodesicity plus all available row incidences yields a linear total
intrinsic size bound. With actual carrier dimensions at most H and s=e,
Larman and the SAME certificate give D + 6*e*2^(H-3), rather than charging
ambient n separately for each selected carrier.

No claim is made that a growing H or the mass bound alone proves Polynomial
Hirsch. New proof candidates, awaiting local Lean/axiom verification.
-/
open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschPolynomialAccess HirschCircuitLocalization HirschRegionRoute
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace HirschRegionRoute

theorem list_cost_sum_le_scaled_mass {α : Type*}
    (ls : List α) (cost mass : α → ℕ) (K : ℕ)
    (h : ∀ x ∈ ls, cost x ≤ K * mass x) :
    (ls.map cost).sum ≤ K * (ls.map mass).sum := by
  induction ls with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    omega

/-- Only this many genuinely large-excess calls can occur. This is not an
estimate for their individual edge costs. -/
theorem list_threshold_count_mul_le_mass {α : Type*}
    (ls : List α) (mass : α → ℕ) (T : ℕ) :
    (ls.filter (fun x => decide (T ≤ mass x))).length * T ≤ (ls.map mass).sum := by
  induction ls with
  | nil => simp
  | cons x xs ih =>
    by_cases hx : T ≤ mass x
    · have h := Nat.add_le_add hx ih
      simpa [hx, Nat.add_mul, Nat.add_comm] using h
    · have h :
          (xs.filter (fun x => decide (T ≤ mass x))).length * T ≤
            mass x + (xs.map mass).sum := by omega
      simpa [hx] using h
end HirschRegionRoute

namespace HirschRadial
variable {d n D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- All selected intrinsic dimensions and minimum row counts have the same
linear aggregate budget. It is not necessary to list unused portal pairs. -/
theorem DeferredClipCertificate.carrier_size_mass_le
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) (hinj : Function.Injective row)
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i, ⟪a (row i), o⟫ < b (row i))
    (defect : ℕ) (hdefect : Fintype.card ι + defect = n-d) :
    ((clipRepairCutLegs c.legs).map fun leg =>
      commonFaceDim a b leg.entry leg.exit).sum ≤
        c.cutSupport.card * defect + 3 * Fintype.card ι ∧
    ((clipRepairCutLegs c.legs).map fun leg =>
      commonFaceMinSubpresentationCount a b leg.entry leg.exit).sum ≤
        2 * (c.cutSupport.card * defect + 3 * Fintype.card ι) := by
  have hm := c.carrier_mass_le a b row hinj hbd o hstrict defect hdefect
  have hd := list_cost_sum_le_scaled_mass (clipRepairCutLegs c.legs)
    (fun leg => commonFaceDim a b leg.entry leg.exit)
    (fun leg => commonFacePresentationExcess a b leg.entry leg.exit) 1 (by
      intro leg hleg
      have hf := c.fits _ ((cut_leg_mem_iff c leg).mp hleg)
      simpa using commonFace_dim_le_minExcess_of_vertices a b leg.entry leg.exit
        hbd hf.1.1 hf.2.1.1)
  have hr := list_cost_sum_le_scaled_mass (clipRepairCutLegs c.legs)
    (fun leg => commonFaceMinSubpresentationCount a b leg.entry leg.exit)
    (fun leg => commonFacePresentationExcess a b leg.entry leg.exit) 2 (by
      intro leg hleg
      have hf := c.fits _ ((cut_leg_mem_iff c leg).mp hleg)
      exact commonFace_minCount_le_two_mul_minExcess_of_vertices a b leg.entry leg.exit
        hbd hf.1.1 hf.2.1.1)
  constructor
  · simpa using hd.trans (Nat.mul_le_mul_left 1 hm)
  · exact hr.trans (Nat.mul_le_mul_left 2 hm)

/-- The carrier dimension cap is applied to the actual selected pairs, not
all pairs on every available facet. The classical Larman input is explicit. -/
theorem DeferredClipCertificate.route_of_all_cut_mass_dim_cap
    (hlar : LarmanHpolyBound)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) (hinj : Function.Injective row)
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i, ⟪a (row i), o⟫ < b (row i))
    (defect : ℕ) (hdefect : Fintype.card ι + defect = n-d)
    (H : ℕ) (hH : ∀ leg ∈ clipRepairCutLegs c.legs,
      commonFaceDim a b leg.entry leg.exit ≤ H) :
    Route (Adj (Hpoly a b))
      (D + (2 * 2^(H-3)) * (c.cutSupport.card * defect + 3 * Fintype.card ι)) u v := by
  let cost := fun (_i : ι) (p q : EuclideanSpace ℝ (Fin d)) =>
    commonFaceMinSubpresentationCount a b p q * 2^(commonFaceDim a b p q-3)
  have hlocal : ∀ leg ∈ clipRepairCutLegs c.legs,
      Route (Adj (Hpoly a b)) (cost leg.label leg.entry leg.exit) leg.entry leg.exit := by
    intro leg hleg
    have hf := c.fits _ ((cut_leg_mem_iff c leg).mp hleg)
    have hd := commonFace_diamLE_minCount_mul_pow_dim hlar a b leg.entry leg.exit
      hbd hf.1.1 hf.2.1.1
    exact extreme_face_region (Hpoly a b) (commonFace a b leg.entry leg.exit)
      (cost leg.label leg.entry leg.exit)
      (commonFace_isExtreme a b leg.entry leg.exit) hd
      leg.entry ⟨hf.1.1, commonFace_u_mem a b _ _ hf.1.1.1⟩
      leg.exit ⟨hf.2.1.1, commonFace_x_mem a b _ _ hf.2.1.1.1⟩
  have hc := list_cost_sum_le_scaled_mass (clipRepairCutLegs c.legs)
    (fun leg => cost leg.label leg.entry leg.exit)
    (fun leg => commonFacePresentationExcess a b leg.entry leg.exit) (2 * 2^(H-3)) (by
      intro leg hleg
      have hf := c.fits _ ((cut_leg_mem_iff c leg).mp hleg)
      have hm := commonFace_minCount_le_two_mul_minExcess_of_vertices
        a b leg.entry leg.exit hbd hf.1.1 hf.2.1.1
      have hp : 2^(commonFaceDim a b leg.entry leg.exit-3) ≤ 2^(H-3) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by have hd := hH leg hleg; omega)
      calc
        cost leg.label leg.entry leg.exit ≤
            (2 * commonFacePresentationExcess a b leg.entry leg.exit) * 2^(H-3) :=
          Nat.mul_le_mul hm hp
        _ = (2 * 2^(H-3)) * commonFacePresentationExcess a b leg.entry leg.exit := by ring)
  have hm := c.carrier_mass_le a b row hinj hbd o hstrict defect hdefect
  have hbound := hc.trans (Nat.mul_le_mul_left (2 * 2^(H-3)) hm)
  obtain ⟨w, hw0, hwB, hs⟩ := c.assemble cost hlocal
  exact HirschProduct.pad_walk _ (Nat.add_le_add_left hbound D) w hw0 hwB hs

/-- All e available cuts, arbitrary used-support deficit: the dimension-five
case improves the former D+(4n+3)e budget to the linear D+24e. -/
theorem DeferredClipCertificate.route_dim_five_all_excess_available
    (hlar : LarmanHpolyBound)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) (hinj : Function.Injective row)
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i, ⟪a (row i), o⟫ < b (row i))
    (hall : Fintype.card ι = n-d)
    (hH : ∀ leg ∈ clipRepairCutLegs c.legs,
      commonFaceDim a b leg.entry leg.exit ≤ 5) :
    Route (Adj (Hpoly a b)) (D + 24 * (n-d)) u v := by
  have h := c.route_of_all_cut_mass_dim_cap hlar a b row hinj hbd o hstrict
    0 (by omega) 5 hH
  norm_num [hall, ← Nat.mul_assoc] at h ⊢
  exact h

#print axioms HirschRegionRoute.list_threshold_count_mul_le_mass
#print axioms DeferredClipCertificate.carrier_size_mass_le
#print axioms DeferredClipCertificate.route_of_all_cut_mass_dim_cap
#print axioms DeferredClipCertificate.route_dim_five_all_excess_available
end HirschRadial
