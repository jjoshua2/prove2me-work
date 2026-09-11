import Mathlib
import Solutions.PolynomialCarrierExcessThreeRouting

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- Variable-budget carrier theorem. If a common carrier has an equivalent
coordinate presentation with row excess `r ≤ 3`, then its intrinsic graph
diameter is at most `r`.  This keeps the exact low-excess cost rather than
rounding every carrier up to three. -/
theorem commonFace_diamLE_of_subpresentation_excess_le_three
    {d n : ℕ}
    (hsmall : SmallExcessHpolyBound)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (r : ℕ) (hr : r ≤ 3)
    (hsub : HirschCommonFace.HasSubpresentationAtMost
      (commonFaceA a b u v) (commonFaceB a b u v)
      (commonFaceDim a b u v + r)) :
    DiamLE (commonFace a b u v) r := by
  obtain ⟨m, hm, e, he⟩ := hsub
  have hbdCoord := commonFace_coord_bounded a b u v hbd
  have hbdSub : Bornology.IsBounded
      (Hpoly (fun j => commonFaceA a b u v (e j))
        (fun j => commonFaceB a b u v (e j))) := by
    rw [he]
    exact hbdCoord
  have hrows : m ≤ commonFaceDim a b u v + 3 := by omega
  have hDsub : DiamLE
      (Hpoly (fun j => commonFaceA a b u v (e j))
        (fun j => commonFaceB a b u v (e j)))
      (m - commonFaceDim a b u v) :=
    hsmall (commonFaceDim a b u v) m
      (fun j => commonFaceA a b u v (e j))
      (fun j => commonFaceB a b u v (e j)) hrows hbdSub
  have hcost : m - commonFaceDim a b u v ≤ r := by omega
  have hDsubR : DiamLE
      (Hpoly (fun j => commonFaceA a b u v (e j))
        (fun j => commonFaceB a b u v (e j))) r := by
    intro x hx y hy
    obtain ⟨w, hw0, hwB, hs⟩ := hDsub x hx y hy
    exact HirschProduct.pad_walk _ hcost w hw0 hwB hs
  have hDcoord :
      DiamLE (Hpoly (commonFaceA a b u v) (commonFaceB a b u v)) r := by
    rw [← he]
    exact hDsubR
  have himage := Hirsch.affineMap_diamLE_image_of_injective
    (commonFaceAffineMap a b u v)
    (commonFaceAffineMap_injective a b u v)
    (Hpoly (commonFaceA a b u v) (commonFaceB a b u v)) r hDcoord
  rw [commonFaceAffineMap_image_coord a b u v] at himage
  exact himage

/-- Exact additive routing certificate for a feasible checkpoint sequence. Each
step supplies its own intrinsic row-excess budget `R i ≤ 3`; the parent edge
route costs the SUM of those budgets, not `3L`.  The ambient parent may have
arbitrary row excess and intermediate checkpoints need not be vertices. -/
theorem feasible_sequence_edge_route_of_carrier_excess_budgets_le_three
    (hsmall : SmallExcessHpolyBound)
    {d n L : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hfeas : ∀ k ≤ L, w k ∈ Hpoly a b)
    (h0 : w 0 ∈ extremePoints ℝ (Hpoly a b))
    (hL : w L ∈ extremePoints ℝ (Hpoly a b))
    (R : Fin L → ℕ) (hR : ∀ i, R i ≤ 3)
    (hsub : ∀ i : Fin L,
      HirschCommonFace.CommonFaceHasSubpresentationAtMost a b
        (w i.val) (w (i.val + 1))
        (commonFaceDim a b (w i.val) (w (i.val + 1)) + R i)) :
    HirschRegionRoute.Route (Adj (Hpoly a b)) (∑ i, R i) (w 0) (w L) := by
  have hP : IsCompact (Hpoly a b) :=
    Metric.isCompact_iff_isClosed_bounded.2 ⟨hpoly_isClosed a b, hbd⟩
  have hB : ∀ i : Fin L,
      DiamLE (commonFace a b (w i.val) (w (i.val + 1))) (R i) := by
    intro i
    exact commonFace_diamLE_of_subpresentation_excess_le_three hsmall a b
      (w i.val) (w (i.val + 1)) hbd (R i) (hR i)
      (by simpa [HirschCommonFace.CommonFaceHasSubpresentationAtMost] using hsub i)
  exact route_of_feasible_commonFace_carrier_budgets
    a b hP w L hfeas h0 hL R hB

#print axioms commonFace_diamLE_of_subpresentation_excess_le_three
#print axioms feasible_sequence_edge_route_of_carrier_excess_budgets_le_three

end HirschCircuitLocalization
