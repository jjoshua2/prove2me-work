import Mathlib

/-!
# Signed component kernels and bounded dual-basis certificates

Rows with two unit coefficients impose z_j = z_i or z_j = -z_i.
An odd-sign cycle pins a whole component without a reference-node row. Removing
one row from a nonsingular signed basis leaves one free signed-constant
component; normalizing its {0,1,-1} kernel vector divides by ±1 or ±2.

The path, normalization and cone certificates below are NEW UNCOMPILED proof
candidates. Extraction of the component certificates from an arbitrary signed
row matrix, and the external Dadush--Haehnle diameter theorem, are NOT claimed
as new kernel-checked declarations by this module.
-/
open scoped BigOperators RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace HirschSignedBasis

/-- false preserves a coordinate, true negates it. -/
def signed (s : Bool) (x : ℝ) : ℝ := if s then -x else x

lemma signed_signed (s t : Bool) (x : ℝ) :
    signed s (signed t x) = signed (Bool.xor s t) x := by
  cases s <;> cases t <;> simp [signed]

/-- Path parity, with no assumption that all closed walks have positive sign. -/
inductive SignedReach {ι : Type*} (link : ι → ι → Bool → Prop) : ι → ι → Bool → Prop
  | refl (i : ι) : SignedReach link i i false
  | step {i j k : ι} {s t : Bool} (edge : link i j s)
      (tail : SignedReach link j k t) : SignedReach link i k (Bool.xor s t)

theorem signed_path_transport {ι : Type*} (link : ι → ι → Bool → Prop)
    (z : ι → ℝ) (heq : ∀ i j s, link i j s → z i = signed s (z j))
    {i j : ι} {s : Bool} (p : SignedReach link i j s) : z i = signed s (z j) := by
  induction p with
  | refl i => simp [signed]
  | @step i j k s t edge tail ih =>
    rw [heq i j s edge, ih, signed_signed]

/-- A negative closed walk is an extra homogeneous equation, not a free
translation component. This is exactly what ordinary network connectivity misses. -/
theorem negative_cycle_pins {ι : Type*} (link : ι → ι → Bool → Prop)
    (z : ι → ℝ) (heq : ∀ i j s, link i j s → z i = signed s (z j))
    (i : ι) (p : SignedReach link i i true) : z i = 0 := by
  have h := signed_path_transport link z heq p
  simp [signed] at h
  linarith

theorem connected_to_pin_zero {ι : Type*} (link : ι → ι → Bool → Prop)
    (z : ι → ℝ) (heq : ∀ i j s, link i j s → z i = signed s (z j))
    {i j : ι} {s : Bool} (p : SignedReach link i j s) (hj : z j = 0) : z i = 0 := by
  have h := signed_path_transport link z heq p
  simpa [hj,signed] using h

/-- A deleted-basis-row kernel witness gives the corresponding inverse column.
The finite checker supplies all these exact equations; no determinant magnitude
is used. -/
theorem normalized_kernel_dual_column {d : ℕ}
    (A : Fin d → (Fin d → ℝ) →ₗ[ℝ] ℝ) (i : Fin d)
    (g : Fin d → ℝ) (hother : ∀ j, j ≠ i → A j g = 0)
    (hi : A i g ≠ 0) :
    ∀ j, A j ((A i g)⁻¹ • g) = if j = i then 1 else 0 := by
  intro j
  by_cases h : j = i
  · subst j
    simp [map_smul,hi]
  · simp [map_smul,hother j h,h]

/-- The actual signed normalization denominators are ±1 or ±2. This gives
an entry bound independent of exponentially large full-basis determinants. -/
theorem normalized_signed_coordinate_bound {d : ℕ}
    (g : Fin d → ℝ) (hg : ∀ j, |g j| ≤ 1) (a : ℝ)
    (ha : a = -2 ∨ a = -1 ∨ a = 1 ∨ a = 2) :
    ∀ j, |((a⁻¹) • g) j| ≤ 1 := by
  intro j
  rcases ha with ha | ha | ha | ha <;> subst a <;>
    simp only [Pi.smul_apply,smul_eq_mul,abs_mul] <;> norm_num <;>
    nlinarith [hg j,abs_nonneg (g j)]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

/-- Explicit finite conic combination, rather than an assumed normal-fan fact. -/
def positiveCone (a : ι → E) : Set E :=
  {x | ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ (∑ i, c i • a i) = x}

/-- A bounded dual frame certifies a whole ball in a normal cone.
For unnormalized signed rows, dual norms are <=sqrt(d); the sum of the row
norms is <=d*sqrt(2). Normalizing the center therefore gives
 tau >= 1/(sqrt(2)*d^(3/2)), as proved in the companion note. -/
theorem dual_frame_ball_in_cone (a u : ι → E) (R : ℝ)
    (hu : ∀ i, ‖u i‖ ≤ R)
    (hexpand : ∀ z : E, (∑ i, ⟪z,u i⟫ • a i) = z)
    (w : E) (hw : ‖w‖ * R ≤ 1) :
    (∑ i, a i) + w ∈ positiveCone a := by
  refine ⟨fun i => 1 + ⟪w,u i⟫, ?_, ?_⟩
  · intro i
    have h := real_inner_le_norm (-w) (u i)
    simp only [inner_neg_left,norm_neg] at h
    have hm := mul_le_mul_of_nonneg_left (hu i) (norm_nonneg w)
    linarith
  · simp only [add_smul,one_smul,Finset.sum_add_distrib,hexpand]

/-- Separation of a row from the span of the other basis rows is certified
by its dual vector. No minimum subdeterminant estimate is required. -/
theorem row_separation_from_dual (a w u : E) (K : ℝ)
    (ha : ⟪a,u⟫ = 1) (hw : ⟪w,u⟫ = 0) (hu : ‖u‖ ≤ K) :
    1 ≤ ‖a-w‖ * K := by
  have h := real_inner_le_norm (a-w) u
  rw [inner_sub_left,ha,hw,sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left hu (norm_nonneg _))

#print axioms signed_path_transport
#print axioms negative_cycle_pins
#print axioms connected_to_pin_zero
#print axioms normalized_kernel_dual_column
#print axioms normalized_signed_coordinate_bound
#print axioms dual_frame_ball_in_cone
#print axioms row_separation_from_dual
end HirschSignedBasis
