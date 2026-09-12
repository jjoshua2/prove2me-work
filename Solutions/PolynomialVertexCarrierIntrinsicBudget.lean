import Solutions.PolynomialLowDimensionalCarrierRouting
import Solutions.PolynomialCommonFaceRoutingModel
import Solutions.PolynomialCommonFaceIntrinsicRowCount
import Solutions.PolynomialSeparatedRows

/-!
# Vertex-pair carrier size and an intrinsic Larman budget

The two actual portal vertices are separated in their smallest common face.
Consequently its minimum row count M and intrinsic dimension h satisfy
2*h <= M, hence h <= delta := M-h and M <= 2*delta.
Unlike the earlier 4*n low-dimensional adapter, the resulting Larman budget
uses M, not the ambient row count n.

This is a new proof candidate. No compiler or platform verdict is asserted.
All classical diameter inputs remain explicit; no target placeholders are used.
-/
open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschPolynomialAccess HirschRegionRoute
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
namespace HirschCircuitLocalization

/-- The minimum intrinsic presentation of a vertex-pair carrier has at least
 twice as many rows as its dimension. The vertex hypotheses are essential. -/
theorem commonFace_two_mul_dim_le_minCount_of_vertices
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    2 * commonFaceDim a b u v ≤ commonFaceMinSubpresentationCount a b u v := by
  obtain ⟨m, _hmn, e, q, he, _hbdSub, hirr, hstrict, h0ext, hqext, hpoint⟩ :=
    commonFace_edgeRefinement_ready_model a b u v hbd hu hv
  have hmin := commonFace_minCount_eq_irredundant_subpresentation
    a b u v e he hirr hstrict
  obtain ⟨q', _hq', hpoint', hsep⟩ :=
    commonFace_coord_endpoint_separation a b u v hu.1 hv.1
  have hqq : q' = q := by
    apply commonFaceAffineMap_injective a b u v
    change commonFacePoint a b u v q' = commonFacePoint a b u v q
    exact hpoint'.trans hpoint.symm
  subst q'
  have htwo := separated_extremes_n_ge_two_d
    (fun j => commonFaceA a b u v (e j))
    (fun j => commonFaceB a b u v (e j)) 0 q h0ext hqext
    (fun j hj => hsep (e j) hj)
  simpa only [hmin] using htwo

/-- A vertex-pair carrier is no higher-dimensional than its own excess. -/
theorem commonFace_dim_le_minExcess_of_vertices
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    commonFaceDim a b u v ≤ commonFacePresentationExcess a b u v := by
  have ht := commonFace_two_mul_dim_le_minCount_of_vertices a b u v hbd hu hv
  unfold commonFacePresentationExcess
  omega

/-- The same minimum presentation has at most twice its excess many rows. -/
theorem commonFace_minCount_le_two_mul_minExcess_of_vertices
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    commonFaceMinSubpresentationCount a b u v ≤
      2 * commonFacePresentationExcess a b u v := by
  have ht := commonFace_two_mul_dim_le_minCount_of_vertices a b u v hbd hu hv
  unfold commonFacePresentationExcess
  omega

/-- Apply the public Larman input to the MINIMUM equivalent presentation.
This avoids paying for original inequalities that vanish or become redundant. -/
theorem commonFace_diamLE_minCount_mul_pow_dim
    (hlar : LarmanHpolyBound) {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    DiamLE (commonFace a b u v)
      (commonFaceMinSubpresentationCount a b u v * 2 ^ (commonFaceDim a b u v - 3)) := by
  obtain ⟨m, _hmn, e, _q, he, hbdSub, hirr, hstrict, h0ext, _hqext, _hpoint⟩ :=
    commonFace_edgeRefinement_ready_model a b u v hbd hu hv
  have hmin := commonFace_minCount_eq_irredundant_subpresentation
    a b u v e he hirr hstrict
  have hcoord := hlar (commonFaceDim a b u v) m
    (fun j => commonFaceA a b u v (e j))
    (fun j => commonFaceB a b u v (e j)) ⟨0, h0ext.1⟩ hbdSub
  rw [he] at hcoord
  have himage := Hirsch.affineMap_diamLE_image_of_injective
    (commonFaceAffineMap a b u v) (commonFaceAffineMap_injective a b u v)
    (Hpoly (commonFaceA a b u v) (commonFaceB a b u v))
    (m * 2 ^ (commonFaceDim a b u v - 3)) hcoord
  rw [commonFaceAffineMap_image_coord a b u v] at himage
  simpa only [hmin] using himage

/-- Excess cap K bounds the actual ordinary-edge diameter independently of n,d.
The cost is exponential in K; no uniform polynomial conclusion is implied. -/
theorem commonFace_diamLE_two_mul_cap_mul_pow
    (hlar : LarmanHpolyBound) {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (K : ℕ) (hcap : commonFacePresentationExcess a b u v ≤ K) :
    DiamLE (commonFace a b u v) ((2*K) * 2 ^ (K-3)) := by
  have hd := (commonFace_dim_le_minExcess_of_vertices a b u v hbd hu hv).trans hcap
  have hm := (commonFace_minCount_le_two_mul_minExcess_of_vertices
    a b u v hbd hu hv).trans (Nat.mul_le_mul_left 2 hcap)
  have hpow : 2 ^ (commonFaceDim a b u v - 3) ≤ 2 ^ (K-3) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hcost := Nat.mul_le_mul hm hpow
  have hdiam := commonFace_diamLE_minCount_mul_pow_dim hlar a b u v hbd hu hv
  intro p hp q hq
  obtain ⟨w, hw0, hwB, hs⟩ := hdiam p hp q hq
  exact HirschProduct.pad_walk _ hcost w hw0 hwB hs

/-- Use exact small-excess routing where available and intrinsic Larman beyond it. -/
def vertexCarrierBudget (K : ℕ) : ℕ :=
  if K ≤ 3 then K else (2*K) * 2 ^ (K-3)

theorem commonFace_diamLE_vertexCarrierBudget
    (hsmall : SmallExcessHpolyBound) (hlar : LarmanHpolyBound) {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (K : ℕ) (hcap : commonFacePresentationExcess a b u v ≤ K) :
    DiamLE (commonFace a b u v) (vertexCarrierBudget K) := by
  unfold vertexCarrierBudget
  split_ifs with hK
  · have hdiam := commonFace_diamLE_minPresentationExcess_of_le_three
      hsmall a b u v hbd hu.1 (hcap.trans hK)
    intro p hp q hq
    obtain ⟨w, hw0, hwB, hs⟩ := hdiam p hp q hq
    exact HirschProduct.pad_walk _ hcap w hw0 hwB hs
  · exact commonFace_diamLE_two_mul_cap_mul_pow hlar a b u v hbd hu hv K hcap

#print axioms commonFace_two_mul_dim_le_minCount_of_vertices
#print axioms commonFace_dim_le_minExcess_of_vertices
#print axioms commonFace_minCount_le_two_mul_minExcess_of_vertices
#print axioms commonFace_diamLE_minCount_mul_pow_dim
#print axioms commonFace_diamLE_two_mul_cap_mul_pow
#print axioms commonFace_diamLE_vertexCarrierBudget
end HirschCircuitLocalization
