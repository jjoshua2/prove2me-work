import Solutions.PolynomialSegmentFiberEquality

/-!
# Global segment-removal certificates and sharp maximality

Positive row combinations certify every opposing-row width, with a single
feasible sharpness point proving the largest removable parameter. The coarse
H-system is derived from the ORIGINAL rows. No supplied decomposition is assumed.

NEW UNCOMPILED candidates. LP optimization/recognition is not asserted to have
been kernel verified merely because these finite certificate statements exist.
-/
open Set HirschSegmentPeeling
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace HirschSegmentPeeling
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {ι : Type*} [Fintype ι]

/-- Farkas evidence for one opposing pair, expressed with exact original rows. -/
structure PairCertificate
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g : E) (τ : ℝ) (i j : ι) where
  weights : ι → ℝ
  nonnegative : ∀ k, 0 ≤ weights k
  normal_identity : ∑ k, weights k • a k = (-a j g) • a i+(a i g) • a j
  constant_bound : (∑ k, weights k*b k) ≤
    (-a j g)*b i+(a i g)*b j-τ*(a i g)*(-a j g)

theorem PairCertificate.pointwise
    {a : ι → E →ₗ[ℝ] ℝ} {b : ι → ℝ} {g : E} {τ : ℝ} {i j : ι}
    (c : PairCertificate a b g τ i j)
    (x : E) (hx : x ∈ halfspaces a b) :
    τ*(a i g)*(-a j g) ≤ (-a j g)*(b i-a i x)+(a i g)*(b j-a j x) := by
  have hs : (∑ k, c.weights k*a k x) ≤ ∑ k, c.weights k*b k := by
    exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hx k) (c.nonnegative k))
  have he := congrArg (fun f : E →ₗ[ℝ] ℝ => f x) c.normal_identity
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.add_apply,smul_eq_mul] at he
  have hb := c.constant_bound
  nlinarith

/-- An exact global model equality follows from finite certificate data. -/
theorem segment_equality_of_farkas
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g : E) (τ : ℝ)
    (hτ : 0 ≤ τ) (hplus : ∃ i, 0 < a i g)
    (cert : ∀ i j, 0 < a i g → a j g < 0 → PairCertificate a b g τ i j) :
    halfspaces a b = segmentSum (erosion a b g τ) g τ := by
  apply segment_equality_of_pair_widths a b g τ hτ hplus
  intro x hx i j hi hj
  exact (cert i j hi hj).pointwise x hx

/-- One sharp opposing-row pair bounds ANY decomposition with the same direction,
not just the endpoint erosion chosen by the algorithm. The unknown summand P
is arbitrary. -/
theorem any_segment_summand_le_sharp_width
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g x : E) (τ s : ℝ)
    (i j : ι) (hi : 0 < a i g) (hj : a j g < 0)
    (hx : x ∈ halfspaces a b)
    (hsharp : (-a j g)*(b i-a i x)+(a i g)*(b j-a j x) = τ*(a i g)*(-a j g))
    (P : Set E) (hs : 0 ≤ s) (hdecomp : halfspaces a b = segmentSum P g s) : s ≤ τ := by
  have hx' : x ∈ segmentSum P g s := by rw [←hdecomp];exact hx
  obtain ⟨p,hp,t,ht0,hts,hxpt⟩ := hx'
  have hp0 : p ∈ halfspaces a b := by
    rw [hdecomp]
    exact ⟨p,hp,0,le_rfl,hs,by simp⟩
  have hp1 : p+s • g ∈ halfspaces a b := by
    rw [hdecomp]
    exact ⟨p,hp,s,hs,le_rfl,rfl⟩
  have hb0 := hp0 j
  have hb1 := hp1 i
  have hix := congrArg (fun z : E => a i z) hxpt
  have hjx := congrArg (fun z : E => a j z) hxpt
  simp only [map_add,map_smul,smul_eq_mul] at hb1 hix hjx
  have hfirst : t*(-a j g) ≤ b j-a j x := by nlinarith
  have hlast : (s-t)*(a i g) ≤ b i-a i x := by nlinarith
  have h₁ := mul_le_mul_of_nonneg_left hfirst hi.le
  have h₂ := mul_le_mul_of_nonneg_left hlast (le_of_lt (neg_pos.mpr hj))
  have hprod : 0 < (a i g)*(-a j g) := mul_pos hi (neg_pos.mpr hj)
  nlinarith [h₁, h₂, hsharp, hprod]

/-- RHS subtraction commutes once two exact extraction amounts are justified.
The stronger invariance of maximal amounts under transverse extraction has a
separate convex-fiber proof in the note; it is not assumed by this identity. -/
theorem erosion_rhs_commutes
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g h : E) (s t : ℝ) :
    (fun i => (b i-s*max (a i g) 0)-t*max (a i h) 0) =
    (fun i => (b i-t*max (a i h) 0)-s*max (a i g) 0) := by
  funext i
  ring

#print axioms PairCertificate.pointwise
#print axioms segment_equality_of_farkas
#print axioms any_segment_summand_le_sharp_width
#print axioms erosion_rhs_commutes
end HirschSegmentPeeling
