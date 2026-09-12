import Solutions.PolynomialMaximalSupportClipping

/-! Discharge low-dimensional selected carriers using the public Larman bound.
The classical input stays explicit, as with `SmallExcessHpolyBound`, so this
adapter is auditable without importing local theorem stubs. -/
open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRegionRoute HirschPolynomialAccess
set_option autoImplicit false
noncomputable section

namespace HirschCircuitLocalization

/-- Exact type of the already-public Larman theorem. -/
def LarmanHpolyBound : Prop :=
  ∀ (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
    (Hpoly a b).Nonempty → Bornology.IsBounded (Hpoly a b) →
    DiamLE (Hpoly a b) (n * 2 ^ (d - 3))

/-- Larman in the intrinsic chart gives cost at most `4*n` for every carrier
of dimension at most five. This does not assume that the parent has low dimension. -/
theorem commonFace_diamLE_four_mul_rows_of_dim_le_five
    (hlar : LarmanHpolyBound) {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hd : commonFaceDim a b u v ≤ 5) :
    DiamLE (commonFace a b u v) (4 * n) := by
  have hcoord : DiamLE (Hpoly (commonFaceA a b u v) (commonFaceB a b u v)) (4*n) := by
    by_cases hne : (Hpoly (commonFaceA a b u v) (commonFaceB a b u v)).Nonempty
    · have hbound := hlar (commonFaceDim a b u v) n
        (commonFaceA a b u v) (commonFaceB a b u v) hne
        (commonFace_coord_bounded a b u v hbd)
      have hpow : 2 ^ (commonFaceDim a b u v - 3) ≤ 4 := by
        have he : commonFaceDim a b u v - 3 ≤ 2 := by omega
        exact (Nat.pow_le_pow_right (by decide : 0 < 2) he)
      have hcost : n * 2 ^ (commonFaceDim a b u v - 3) ≤ 4*n := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left n hpow
      intro p hp q hq
      obtain ⟨w, hw0, hwB, hs⟩ := hbound p hp q hq
      exact HirschProduct.pad_walk _ hcost w hw0 hwB hs
    · intro p hp
      exact False.elim (hne ⟨p, hp.1⟩)
  have himage := Hirsch.affineMap_diamLE_image_of_injective
    (commonFaceAffineMap a b u v) (commonFaceAffineMap_injective a b u v)
    (Hpoly (commonFaceA a b u v) (commonFaceB a b u v)) (4*n) hcoord
  rwa [commonFaceAffineMap_image_coord a b u v] at himage

#print axioms commonFace_diamLE_four_mul_rows_of_dim_le_five
end HirschCircuitLocalization

namespace HirschRadial
open HirschCircuitLocalization

/-- Low dimension and low excess may vary from leg to leg. If each actual
selected carrier has either certificate, all cut calls close with a uniform
linear local budget, yielding a quadratic total budget when at most `n-d`
cuts are used. -/
theorem DeferredClipCertificate.route_of_used_carriers_low_dimension_or_excess
    (hsmall : SmallExcessHpolyBound) (hlar : LarmanHpolyBound)
    {d n D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (heasy : ∀ leg ∈ clipRepairCutLegs c.legs,
      commonFacePresentationExcess a b leg.entry leg.exit ≤ 3 ∨
        commonFaceDim a b leg.entry leg.exit ≤ 5) :
    Route (Adj (Hpoly a b)) (D + (4*n+3) * c.cutSupport.card) u v := by
  have hlocal : ∀ leg ∈ clipRepairCutLegs c.legs,
      Route (Adj (Hpoly a b)) (4*n+3) leg.entry leg.exit := by
    intro leg hleg
    have hf := c.fits _ ((cut_leg_mem_iff c leg).mp hleg)
    have hdiam : DiamLE (commonFace a b leg.entry leg.exit) (4*n+3) := by
      rcases heasy leg hleg with he | hd
      · have hbound := commonFace_diamLE_minPresentationExcess_of_le_three
          hsmall a b leg.entry leg.exit hbd hf.1.1.1 he
        intro p hp q hq
        obtain ⟨w, hw0, hwB, hs⟩ := hbound p hp q hq
        exact HirschProduct.pad_walk _ (by omega) w hw0 hwB hs
      · have hbound := commonFace_diamLE_four_mul_rows_of_dim_le_five
          hlar a b leg.entry leg.exit hbd hd
        intro p hp q hq
        obtain ⟨w, hw0, hwB, hs⟩ := hbound p hp q hq
        exact HirschProduct.pad_walk _ (by omega) w hw0 hwB hs
    exact extreme_face_region (Hpoly a b) (commonFace a b leg.entry leg.exit) (4*n+3)
      (commonFace_isExtreme a b leg.entry leg.exit) hdiam
      leg.entry ⟨hf.1.1, commonFace_u_mem a b _ _ hf.1.1.1⟩
      leg.exit ⟨hf.2.1.1, commonFace_x_mem a b _ _ hf.2.1.1.1⟩
  have hr := c.assemble (fun _ _ _ => 4*n+3) hlocal
  rw [c.cutSupport_card]
  simpa [Nat.mul_comm] using hr

#print axioms DeferredClipCertificate.route_of_used_carriers_low_dimension_or_excess
end HirschRadial
