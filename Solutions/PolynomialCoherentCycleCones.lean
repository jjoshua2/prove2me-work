import Solutions.PolynomialSignedBasisGeometry

/-!
# Positive cycle cancellation, rather than a bound on every inverse entry

A coherently directed cycle can have an arbitrarily small gain defect without
making its normal cone narrow. The positive coefficients of its small row sum
are essential. These finite dual-frame lemmas certify an actual ball in the
cone and its transfer under a linear coordinate map.

NEW UNCOMPILED proof candidates. The all-basis balanced/coherent block classification and the
external wide-normal-fan diameter theorem are proved/cited in the note, not
silently introduced as Lean axioms by this module.
-/
open scoped BigOperators RealInnerProductSpace
open Set HirschSignedBasis
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HirschCoherentCone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

/-- Coherent orientations make the open-chain rows telescope. -/
theorem chain_row_sum (v : ℕ → E) (n : ℕ) :
    (∑ i ∈ Finset.range n, (v (i+1)-v i)) = v n-v 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    abel

/-- The closing gain contributes only a scalar defect at one coordinate. -/
theorem coherent_cycle_row_sum (v : ℕ → E) (n : ℕ) (g : ℝ) :
    (∑ i ∈ Finset.range n, (v (i+1)-v i)) + (v 0-g • v n) =
      (1-g) • v n := by
  rw [chain_row_sum]
  module

/-- Even when gamma is tiny, its normalized ray has a POSITIVE representation
in the cycle cone. Replacing the row signs can invalidate this statement. -/
theorem normalized_cycle_ray_mem (a : ι → E) (v : E) (γ : ℝ)
    (hγ : γ ≠ 0) (hsum : (∑ i,a i)=γ • v) :
    (γ / |γ|) • v ∈ positiveCone a := by
  refine ⟨fun _ => |γ|⁻¹, fun _ => inv_nonneg.mpr (abs_nonneg γ), ?_⟩
  rw [←Finset.smul_sum,hsum,smul_smul]
  congr 1
  field_simp

/-- The same small denominator occurs in the dual norm and the positive
coefficient of the center. Cancelling it avoids the old cycle-gap loss. -/
theorem gap_cancels_dual_margin (q norm margin A : ℝ)
    (hq : 0 < q) (hbound : q*norm ≤ A) (hmargin : q*margin=1) :
    norm ≤ A*margin := by
  have hm : 0 < margin := by nlinarith
  have he := congrArg (fun t : ℝ => norm*t) hmargin
  calc
    norm = (q*norm)*margin := by nlinarith [he]
    _ ≤ A*margin := mul_le_mul_of_nonneg_right hbound hm.le

/-- The certificate verifier uses squared rational margins, avoiding numerical
square roots. Nonnegative signs must be checked before comparing squares. -/
theorem margin_from_squared (margin r u c : ℝ)
    (hm : 0 ≤ margin) (hr : 0 ≤ r) (hu : 0 ≤ u) (hc : 0 ≤ c)
    (hsq : (r*u*c)^2 ≤ margin^2) : r*u*c ≤ margin := by
  have ht : 0 ≤ r*u*c := mul_nonneg (mul_nonneg hr hu) hc
  nlinarith

/-- An explicit dual frame and positive margins give the WHOLE ball in the
normal cone, even when the dual vectors individually have huge norm. -/
theorem dual_margin_ball (a dual : ι → E) (c : E) (r : ℝ)
    (hexpand : ∀ z : E, (∑ i, ⟪z,dual i⟫ • a i)=z)
    (hmargin : ∀ i, r*‖dual i‖ ≤ ⟪c,dual i⟫)
    (w : E) (hw : ‖w‖ ≤ r) : c+w ∈ positiveCone a := by
  refine ⟨fun i => ⟪c+w,dual i⟫, ?_, hexpand (c+w)⟩
  intro i
  have h := real_inner_le_norm (-w) (dual i)
  simp only [inner_neg_left,norm_neg] at h
  have hn := mul_le_mul_of_nonneg_right hw (norm_nonneg (dual i))
  have hm := hmargin i
  change 0 ≤ ⟪c+w,dual i⟫
  rw [inner_add_left]
  linarith

section Map
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Transfer finite cone evidence without assuming a graph isomorphism. -/
theorem cone_map_mem (T : E →ₗ[ℝ] F) (a : ι → E) {x : E}
    (hx : x ∈ positiveCone a) : T x ∈ positiveCone (fun i => T (a i)) := by
  obtain ⟨coeff,hpos,hsum⟩ := hx
  refine ⟨coeff,hpos,?_⟩
  have h := congrArg T hsum
  simpa only [map_sum,map_smul] using h

/-- A basis-dependent diagonal gauge must be transported back to the SAME
ambient metric before using any uniform normal-fan theorem. -/
theorem cone_ball_transport (T : E ≃ₗ[ℝ] F) (a : ι → E) (c : E)
    (r K : ℝ) (hK : 0 < K)
    (hinv : ∀ z : F, ‖T.symm z‖ ≤ K*‖z‖)
    (hball : ∀ w : E, ‖w‖ ≤ r → c+w ∈ positiveCone a)
    (z : F) (hz : ‖z‖ ≤ r/K) :
    T c+z ∈ positiveCone (fun i => T (a i)) := by
  have hk := mul_le_mul_of_nonneg_left hz hK.le
  have hnorm : ‖T.symm z‖ ≤ r := by
    have h := (hinv z).trans hk
    have he : K*(r/K)=r := by field_simp
    simpa only [he] using h
  have h := cone_map_mem T.toLinearMap a (hball (T.symm z) hnorm)
  simpa only [LinearEquiv.coe_coe,map_add,LinearEquiv.apply_symm_apply] using h
end Map

#print axioms chain_row_sum
#print axioms coherent_cycle_row_sum
#print axioms normalized_cycle_ray_mem
#print axioms gap_cancels_dual_margin
#print axioms margin_from_squared
#print axioms dual_margin_ball
#print axioms cone_map_mem
#print axioms cone_ball_transport
end HirschCoherentCone
