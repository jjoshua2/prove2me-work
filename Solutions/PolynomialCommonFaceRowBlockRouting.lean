import Mathlib
import Solutions.PolynomialRowBlockRouting
import Solutions.PolynomialLowerExcessCarrierRecursion

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- A minimum equivalent common-carrier presentation which splits, after an
invertible linear coordinate change, into independent row blocks of excess at
most three has intrinsic graph diameter at most exactly its minimum
presentation excess.

This is the direct bridge from the high-excess row-block theorem to the
circuit-carrier induction.  Total carrier excess may be arbitrarily large; the
hypothesis is structural factorization of the *minimum* carrier presentation,
not a small-total-excess assumption. -/
theorem commonFace_diamLE_minPresentationExcess_of_small_row_blocks
    (hsmall : SmallExcessHpolyBound)
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ Hpoly a b)
    (e : Fin (commonFaceMinSubpresentationCount a b u v) ↪ Fin n)
    (heq :
      Hpoly
          (fun j => commonFaceA a b u v (e j))
          (fun j => commonFaceB a b u v (e j)) =
        Hpoly (commonFaceA a b u v) (commonFaceB a b u v))
    {k : ℕ} (dims counts : Fin k → ℕ)
    (T : EuclideanSpace ℝ (Fin (commonFaceDim a b u v)) ≃ₗ[ℝ]
      (∀ i : Fin k, EuclideanSpace ℝ (Fin (dims i))))
    (rowEquiv :
      (Σ i : Fin k, Fin (counts i)) ≃
        Fin (commonFaceMinSubpresentationCount a b u v))
    (A : ∀ i : Fin k, Fin (counts i) → EuclideanSpace ℝ (Fin (dims i)))
    (hrows : ∀ z i j,
      ⟪commonFaceA a b u v (e (rowEquiv ⟨i, j⟩)), T.symm z⟫ =
        ⟪A i j, z i⟫)
    (hcount : ∀ i, dims i ≤ counts i)
    (hsmallcount : ∀ i, counts i ≤ dims i + 3) :
    DiamLE (commonFace a b u v)
      (commonFaceMinSubpresentationCount a b u v - commonFaceDim a b u v) := by
  classical
  let M := commonFaceMinSubpresentationCount a b u v
  let h := commonFaceDim a b u v
  have hzeroFull :
      (0 : EuclideanSpace ℝ (Fin h)) ∈
        Hpoly (commonFaceA a b u v) (commonFaceB a b u v) := by
    apply (mem_commonFace_coord_iff a b u v 0).2
    simpa [commonFacePoint, h] using commonFace_u_mem a b u v hu
  have hzeroSub :
      (0 : EuclideanSpace ℝ (Fin h)) ∈
        Hpoly
          (fun j => commonFaceA a b u v (e j))
          (fun j => commonFaceB a b u v (e j)) := by
    intro j
    exact hzeroFull (e j)
  have hbdCoord := commonFace_coord_bounded a b u v hbd
  have hbdSub : Bornology.IsBounded
      (Hpoly
        (fun j => commonFaceA a b u v (e j))
        (fun j => commonFaceB a b u v (e j))) := by
    rw [heq]
    exact hbdCoord
  have hDsub :
      DiamLE
        (Hpoly
          (fun j => commonFaceA a b u v (e j))
          (fun j => commonFaceB a b u v (e j))) (M - h) := by
    exact HirschRowBlocks.hpoly_diamLE_excess_of_small_row_blocks
      (fun {d n} a b hbd hrows => hsmall d n a b hrows hbd)
      dims counts
      (fun j => commonFaceA a b u v (e j))
      (fun j => commonFaceB a b u v (e j))
      T rowEquiv A hrows hbdSub ⟨0, hzeroSub⟩ hcount hsmallcount
  have hDcoord :
      DiamLE (Hpoly (commonFaceA a b u v) (commonFaceB a b u v)) (M - h) := by
    rw [← heq]
    exact hDsub
  have himage := Hirsch.affineMap_diamLE_image_of_injective
    (commonFaceAffineMap a b u v)
    (commonFaceAffineMap_injective a b u v)
    (Hpoly (commonFaceA a b u v) (commonFaceB a b u v)) (M - h) hDcoord
  rw [commonFaceAffineMap_image_coord a b u v] at himage
  simpa [M, h] using himage

#print axioms commonFace_diamLE_minPresentationExcess_of_small_row_blocks

end HirschCircuitLocalization
