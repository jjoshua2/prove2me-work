import Solutions.PolynomialLowExcessSectionDescent
import Solutions.PolynomialLowDimensionalCarrierRouting

/-! Classical equality-section descent with a Larman base at fixed row excess.
The inputs are the already-Proved facet reduction and Larman propositions.
This bound is exponential in excess, not a uniform polynomial Hirsch bound. -/
open Set Hirsch HirschPolynomialAccess
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace HirschLowExcess
open HirschCircuitLocalization

def excessLarmanBudget (E : ℕ) : ℕ := 2 * E * 2 ^ (E - 3)

/-- When `n<=d+E`, descend through a shared nonzero tight row until `d<=E`.
Then at most `2E` inequalities remain, so Larman costs at most this fixed
function of E. The descent adds neither access steps nor a multiplicative cost. -/
theorem hpoly_diamLE_fixed_excess_larman
    (hlar : LarmanHpolyBound) (hfacet : FacetWalkReduction) (E : ℕ) :
    ∀ (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      n ≤ d + E → Bornology.IsBounded (Hpoly a b) →
      DiamLE (Hpoly a b) (excessLarmanBudget E) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro n a b hrows hbd
    by_cases hd : d ≤ E
    · by_cases hne : (Hpoly a b).Nonempty
      · have hbound := hlar d n a b hne hbd
        have hcost : n * 2 ^ (d-3) ≤ excessLarmanBudget E := by
          apply Nat.mul_le_mul (show n ≤ 2*E by omega)
          exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
        intro u hu v hv
        obtain ⟨w, hw0, hwB, hs⟩ := hbound u hu v hv
        exact HirschProduct.pad_walk _ hcost w hw0 hwB hs
      · intro u hu
        exact False.elim (hne ⟨u, hu.1⟩)
    · intro u hu v hv
      have hsub : n < 2*d := by omega
      obtain ⟨i, hai, hui, hvi⟩ :=
        vertices_share_nonzero_tight_row_of_n_lt_two_d a b u v hu hv hsub
      cases n with
      | zero => exact Fin.elim0 i
      | succ k =>
        have hlow : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d-1))) (b' : Fin k → ℝ),
            Bornology.IsBounded (Hpoly a' b') →
            DiamLE (Hpoly a' b') (excessLarmanBudget E) := by
          intro a' b' hbd'
          exact ih (d-1) (by omega) k a' b' (by omega) hbd'
        have huF : u ∈ extremePoints ℝ
            {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i} := by
          refine ⟨⟨hu.1, hui⟩, ?_⟩
          intro x hx y hy hseg
          exact hu.2 hx.1 hy.1 hseg
        have hvF : v ∈ extremePoints ℝ
            {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i} := by
          refine ⟨⟨hv.1, hvi⟩, ?_⟩
          intro x hx y hy hseg
          exact hv.2 hx.1 hy.1 hseg
        exact hfacet d k a b i hai hbd (excessLarmanBudget E) hlow u v huF hvF

#print axioms hpoly_diamLE_fixed_excess_larman
end HirschLowExcess

namespace HirschCircuitLocalization
open HirschLowExcess

/-- Apply fixed-excess descent to a minimum equivalent carrier presentation,
then transport its ordinary-edge diameter through the intrinsic affine chart. -/
theorem commonFace_diamLE_fixed_excess_larman
    (hlar : LarmanHpolyBound) (hfacet : FacetWalkReduction)
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (E : ℕ) (he : commonFacePresentationExcess a b u v ≤ E) :
    DiamLE (commonFace a b u v) (excessLarmanBudget E) := by
  have hspec := commonFaceMinSubpresentation_spec a b u v
  change HirschCommonFace.HasSubpresentationAtMost
    (commonFaceA a b u v) (commonFaceB a b u v)
    (commonFaceMinSubpresentationCount a b u v) at hspec
  obtain ⟨m, hm, row, hsame⟩ := hspec
  have hrows : m ≤ commonFaceDim a b u v + E := by
    unfold commonFacePresentationExcess at he
    omega
  have hbdSub : Bornology.IsBounded
      (Hpoly (fun j => commonFaceA a b u v (row j))
        (fun j => commonFaceB a b u v (row j))) := by
    rw [hsame]
    exact commonFace_coord_bounded a b u v hbd
  have hsub := hpoly_diamLE_fixed_excess_larman hlar hfacet E
    (commonFaceDim a b u v) m
    (fun j => commonFaceA a b u v (row j))
    (fun j => commonFaceB a b u v (row j)) hrows hbdSub
  rw [hsame] at hsub
  have himage := Hirsch.affineMap_diamLE_image_of_injective
    (commonFaceAffineMap a b u v) (commonFaceAffineMap_injective a b u v)
    (Hpoly (commonFaceA a b u v) (commonFaceB a b u v)) (excessLarmanBudget E) hsub
  rwa [commonFaceAffineMap_image_coord a b u v] at himage

theorem commonFace_diamLE_sixteen_of_excess_le_four
    (hlar : LarmanHpolyBound) (hfacet : FacetWalkReduction)
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (he : commonFacePresentationExcess a b u v ≤ 4) :
    DiamLE (commonFace a b u v) 16 := by
  simpa [excessLarmanBudget] using
    commonFace_diamLE_fixed_excess_larman hlar hfacet a b u v hbd 4 he

#print axioms commonFace_diamLE_fixed_excess_larman
#print axioms commonFace_diamLE_sixteen_of_excess_le_four
end HirschCircuitLocalization
