import Solutions.PolynomialLinearFeedbackMassRouting

/-! A linear route or an actual selected high-dimensional non-feedback carrier.
The residual is failure of this sufficient criterion, not a diameter lower bound. -/
open Set Hirsch HirschRegionRoute HirschRadial HirschPolynomialAccess
open HirschCircuitLocalization HirschPositiveBoxes HirschTargetDeletion
open scoped BigOperators RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace HirschRadial

/-- Mix arbitrary-dimensional feedback carriers with dimension-at-most-five
carriers. Both spend at most eight times their actual presentation excess. -/
theorem DeferredClipCertificate.route_feedback_or_dim_five_of_all_row_mass
    (hlar : LarmanHpolyBound)
    {d n D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) (hinj : Function.Injective row)
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i, ⟪a (row i), o⟫ < b (row i))
    (hall : Fintype.card ι = n-d)
    (heasy : ∀ leg ∈ clipRepairCutLegs c.legs,
      Nonempty (PositiveBoxImage (commonFace a b leg.entry leg.exit)
        (commonFaceDim a b leg.entry leg.exit)) ∨
      commonFaceDim a b leg.entry leg.exit ≤ 5) :
    Route (Adj (Hpoly a b)) (D + 24*(n-d)) u v := by
  let cost := fun (_i : ι) (p q : EuclideanSpace ℝ (Fin d)) =>
    8 * commonFacePresentationExcess a b p q
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
    rcases heasy leg hleg with hm | hdim
    · obtain ⟨m⟩ := hm
      have hd := commonFace_dim_le_minExcess_of_vertices a b leg.entry leg.exit
        hbd hf.1.1 hf.2.1.1
      obtain ⟨w, h0, hB, hs⟩ := hroute _ m.diamLE
      exact HirschProduct.pad_walk _ (by dsimp [cost]; omega) w h0 hB hs
    · have hd := commonFace_diamLE_minCount_mul_pow_dim hlar a b leg.entry leg.exit
        hbd hf.1.1 hf.2.1.1
      have hm := commonFace_minCount_le_two_mul_minExcess_of_vertices
        a b leg.entry leg.exit hbd hf.1.1 hf.2.1.1
      have hp : 2^(commonFaceDim a b leg.entry leg.exit-3) ≤ 4 := by
        calc
          _ ≤ 2^2 := Nat.pow_le_pow_right (by decide) (by omega)
          _ = 4 := by norm_num
      have hc := Nat.mul_le_mul hm hp
      obtain ⟨w, h0, hB, hs⟩ := hroute _ hd
      exact HirschProduct.pad_walk _ (by dsimp [cost]; nlinarith) w h0 hB hs
  have hm := c.carrier_mass_le a b row hinj hbd o hstrict 0 (by omega)
  have hc := list_cost_sum_le_scaled_mass (clipRepairCutLegs c.legs)
    (fun leg => cost leg.label leg.entry leg.exit)
    (fun leg => commonFacePresentationExcess a b leg.entry leg.exit) 8
    (by intro leg _; exact le_rfl)
  obtain ⟨w, h0, hB, hs⟩ := c.assemble cost hlocal
  exact HirschProduct.pad_walk _ (by simp only [Nat.mul_zero, zero_add, hall] at hm; omega)
    w h0 hB hs

end HirschRadial
namespace HirschTargetDeletion

/-- An automatic full-availability certificate either produces a linear route
or exhibits one of its own selected carriers of dimension at least six with
no positive-feedback image model. It retains the joint excess bound. -/
theorem automatic_basis_linear_route_or_high_dim_nonfeedback_carrier
    (hlar : LarmanHpolyBound) {d n : ℕ}
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
        (Route (Adj (Hpoly a b)) (1+24*(n-d)) v u ∨
          ∃ leg ∈ clipRepairCutLegs c.legs,
            6 ≤ commonFaceDim a b leg.entry leg.exit ∧
            ¬ Nonempty (PositiveBoxImage (commonFace a b leg.entry leg.exit)
              (commonFaceDim a b leg.entry leg.exit))) := by
  classical
  obtain ⟨e, c, hm⟩ := exists_automatic_basis_star_linear_mass a b v hv hbd o hstrict u hu
  refine ⟨e, c, hm, ?_⟩
  by_cases heasy : ∀ leg ∈ clipRepairCutLegs c.legs,
      Nonempty (PositiveBoxImage (commonFace a b leg.entry leg.exit)
        (commonFaceDim a b leg.entry leg.exit)) ∨
      commonFaceDim a b leg.entry leg.exit ≤ 5
  · left
    have hc : Fintype.card (basisRemainingRows e) = n-d := by
      simpa only [Fintype.card_coe] using basisRemainingRows_card e
    exact c.route_feedback_or_dim_five_of_all_row_mass hlar a b
      Subtype.val Subtype.val_injective hbd o (fun i => hstrict i.1) hc heasy
  · right
    push Not at heasy
    obtain ⟨leg, hleg, hmodel, hdim⟩ := heasy
    exact ⟨leg, hleg, by omega, fun ⟨m⟩ => hmodel.false m⟩

#print axioms HirschRadial.DeferredClipCertificate.route_feedback_or_dim_five_of_all_row_mass
#print axioms automatic_basis_linear_route_or_high_dim_nonfeedback_carrier
end HirschTargetDeletion
