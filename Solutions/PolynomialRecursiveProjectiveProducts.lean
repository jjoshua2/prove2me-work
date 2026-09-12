import Solutions.PolynomialProjectiveRowBlockRouting
import Solutions.PolynomialMaximalSupportClipping

/-!
# Recursive projective product certificates with telescoping edge budgets

Each node may use its OWN positive projective chart. This is strictly more
flexible than one chart exposing all small-excess factors. Node hypotheses are
actual row identities, affine equivalences and denominator signs; leaves use
only boundedness and the known small-excess row-count condition.

The small-excess theorem is explicit. No conjectural diameter child is added.
This continuation depends on #203's geometric transport interface; the NEW
source here awaits its separate Lean gate.
-/
open Set Hirsch HirschPerspective HirschProjectiveBlocks
open scoped BigOperators RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace HirschRecursiveProducts

/-- A finite geometry certificate, not a diameter hypothesis. Proper positive-
dimensional factors prevent a split from merely restating the same instance.
Affine steps cover translations/recentering without changing n or d. -/
inductive ProductTree : {d n : ℕ} →
    (Fin n → EuclideanSpace ℝ (Fin d)) → (Fin n → ℝ) → Prop
  | leaf {d n : ℕ}
      {a : Fin n → EuclideanSpace ℝ (Fin d)} {b : Fin n → ℝ}
      (hbd : Bornology.IsBounded (Hpoly a b)) (hcount : n ≤ d + 3) :
      ProductTree a b
  | affine {d n : ℕ}
      {a a' : Fin n → EuclideanSpace ℝ (Fin d)} {b b' : Fin n → ℝ}
      (f : EuclideanSpace ℝ (Fin d) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin d))
      (himage : f '' Hpoly a b = Hpoly a' b')
      (prior : ProductTree a b) : ProductTree a' b'
  | split {d n k : ℕ}
      (dims counts : Fin k → ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
      (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ]
        (∀ i : Fin k, EuclideanSpace ℝ (Fin (dims i))))
      (e : (Σ i : Fin k, Fin (counts i)) ≃ Fin n)
      (A : ∀ i : Fin k, Fin (counts i) → EuclideanSpace ℝ (Fin (dims i)))
      (hrows : ∀ z i j, ⟪a (e ⟨i,j⟩), T.symm z⟫ = ⟪A i j, z i⟫)
      (hcount : ∀ i, dims i ≤ counts i)
      (hk : 2 ≤ k) (hdim : ∀ i, 0 < dims i)
      (c : EuclideanSpace ℝ (Fin d))
      (hsource : Hpoly a b ⊆ positiveDomain (rowFunctional c))
      (htarget : Hpoly (shearRows a b c) b ⊆ positiveDomain (-rowFunctional c))
      (children : ∀ i, ProductTree (A i) (fun j => b (e ⟨i,j⟩))) :
      ProductTree (shearRows a b c) b

/-- Sum all leaf excesses exactly once. Products ADD costs and projective/affine
transport preserves them, so no cost multiplier appears at an internal node. -/
theorem ProductTree.diamLE
    (hsmall : ∀ {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
      (b : Fin n → ℝ), Bornology.IsBounded (Hpoly a b) →
      n ≤ d + 3 → DiamLE (Hpoly a b) (n-d))
    {d n : ℕ} {a : Fin n → EuclideanSpace ℝ (Fin d)} {b : Fin n → ℝ}
    (cert : ProductTree a b) : DiamLE (Hpoly a b) (n-d) := by
  induction cert with
  | leaf hbd hcount => exact hsmall _ _ hbd hcount
  | affine f himage prior ih =>
      have h := Hirsch.affineEquiv_diamLE_image f _ _ ih
      rwa [himage] at h
  | split dims counts a b T e A hrows hcount hk hdim c hsource htarget children ih =>
      have hprod := HirschProduct.diamLE_pi
        (fun i => Hpoly (A i) (fun j => b (e ⟨i,j⟩)))
        (fun i => counts i - dims i) ih
      rw [HirschRowBlocks.row_block_excess_sum dims counts T e hcount] at hprod
      rw [← HirschRowBlocks.image_hpoly_eq_pi_of_row_blocks
        dims counts a b T e A hrows] at hprod
      have hbase := (Hirsch.affineEquiv_diamLE_image_iff
        T.toAffineEquiv (Hpoly a b) _).mp hprod
      exact hpoly_diamLE_of_positive_shear a b c _ hsource htarget hbase

/-- The same sufficient criterion is applicable only to the ACTUAL selected
portal pairs. An equivalent intrinsic row model is supplied with at most n
rows; no routing obligation for unused pairs or faces is introduced. -/
theorem carrier_diamLE_rows_of_recursive_projective_model
    (hsmall : ∀ {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
      (b : Fin n → ℝ), Bornology.IsBounded (Hpoly a b) →
      n ≤ d + 3 → DiamLE (Hpoly a b) (n-d))
    {d n m : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (A : Fin m → EuclideanSpace ℝ (Fin (HirschPolynomialAccess.commonFaceDim a b u v)))
    (B : Fin m → ℝ)
    (hmodel : Hpoly A B = Hpoly
      (HirschPolynomialAccess.commonFaceA a b u v)
      (HirschPolynomialAccess.commonFaceB a b u v))
    (cert : ProductTree A B) (hm : m ≤ n) :
    DiamLE (HirschPolynomialAccess.commonFace a b u v) n := by
  have hlocal := ProductTree.diamLE hsmall cert
  have hcoord : DiamLE (Hpoly A B) n := by
    intro p hp q hq
    obtain ⟨w, hw0, hwB, hs⟩ := hlocal p hp q hq
    exact HirschProduct.pad_walk _ (by omega) w hw0 hwB hs
  rw [hmodel] at hcoord
  have himage := Hirsch.affineMap_diamLE_image_of_injective
    (HirschCircuitLocalization.commonFaceAffineMap a b u v)
    (HirschCircuitLocalization.commonFaceAffineMap_injective a b u v)
    (Hpoly (HirschPolynomialAccess.commonFaceA a b u v)
      (HirschPolynomialAccess.commonFaceB a b u v)) n hcoord
  rwa [HirschCircuitLocalization.commonFaceAffineMap_image_coord a b u v] at himage

/-- Actual-cost clipping specialization. The local geometry certificates imply
all selected routes; their number is exactly the cut support cardinality. -/
theorem route_of_used_recursive_projective_carriers
    (hsmall : ∀ {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
      (b : Fin n → ℝ), Bornology.IsBounded (Hpoly a b) →
      n ≤ d + 3 → DiamLE (Hpoly a b) (n-d))
    {d n D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) {u v : EuclideanSpace ℝ (Fin d)}
    (c : HirschRadial.DeferredClipCertificate (Hpoly a b)
      (fun i => a (row i)) (fun i => b (row i)) D u v)
    (hmodels : ∀ leg ∈ HirschRadial.clipRepairCutLegs c.legs,
      ∃ m : ℕ, m ≤ n ∧
        ∃ A : Fin m → EuclideanSpace ℝ
          (Fin (HirschPolynomialAccess.commonFaceDim a b leg.entry leg.exit)),
        ∃ B : Fin m → ℝ,
          Hpoly A B = Hpoly
            (HirschPolynomialAccess.commonFaceA a b leg.entry leg.exit)
            (HirschPolynomialAccess.commonFaceB a b leg.entry leg.exit) ∧
          ProductTree A B) :
    HirschRegionRoute.Route (Adj (Hpoly a b)) (D + n * c.cutSupport.card) u v := by
  have hlegs : ∀ leg ∈ HirschRadial.clipRepairCutLegs c.legs,
      HirschRegionRoute.Route (Adj (Hpoly a b)) n leg.entry leg.exit := by
    intro leg hleg
    obtain ⟨m, hm, A, B, he, ht⟩ := hmodels leg hleg
    have hdiam := carrier_diamLE_rows_of_recursive_projective_model
      hsmall a b leg.entry leg.exit A B he ht hm
    have hf := c.fits _ ((HirschRadial.cut_leg_mem_iff c leg).mp hleg)
    exact HirschRegionRoute.extreme_face_region (Hpoly a b)
      (HirschPolynomialAccess.commonFace a b leg.entry leg.exit) n
      (HirschPolynomialAccess.commonFace_isExtreme a b leg.entry leg.exit) hdiam
      leg.entry ⟨hf.1.1, HirschPolynomialAccess.commonFace_u_mem a b _ _ hf.1.1.1⟩
      leg.exit ⟨hf.2.1.1, HirschPolynomialAccess.commonFace_x_mem a b _ _ hf.2.1.1.1⟩
  have hr := c.assemble (fun _ _ _ => n) hlegs
  rw [c.cutSupport_card]
  simpa [Nat.mul_comm] using hr

#print axioms ProductTree.diamLE
#print axioms carrier_diamLE_rows_of_recursive_projective_model
#print axioms route_of_used_recursive_projective_carriers
end HirschRecursiveProducts
