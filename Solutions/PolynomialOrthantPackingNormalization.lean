import Solutions.PolynomialPositivePerspective

/-!
# Positive projective packing normalization of a bounded orthant model

New uncompiled proof candidate. The input is the exact simple-vertex slack
model {x >= 0 : R_i x <= 1}; R may have negative entries. A nonnegative
combination of its rows with strictly positive combined normal certifies
boundedness and BOTH signs needed for a projective equivalence. No routing
premise is concealed in the normalization certificate.

The general affine slack-coordinate preparation and the classical reduction
to simple polytopes are explained in the paper note, not claimed as additional
Lean declarations here. This is not a proof of Polynomial Hirsch.
-/
open scoped BigOperators
open Set Hirsch HirschPerspective
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace HirschPacking

variable {d m : ℕ}

/-- Coordinate row evaluation as a linear functional. -/
def lin (c : Fin d → ℝ) : (Fin d → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ j, c j * x j
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' r x := by simp [mul_left_comm, Finset.mul_sum]

lemma lin_add_apply (a c x : Fin d → ℝ) :
    lin (a + c) x = lin a x + lin c x := by
  simp [lin, add_mul, Finset.sum_add_distrib]

lemma lin_nonneg (c x : Fin d → ℝ)
    (hc : ∀ j, 0 ≤ c j) (hx : ∀ j, 0 ≤ x j) : 0 ≤ lin c x :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (hc j) (hx j))

/-- All original upper rows are present; no redundancy removal is implicit. -/
def orthantModel (R : Fin m → Fin d → ℝ) : Set (Fin d → ℝ) :=
  {x | (∀ j, 0 ≤ x j) ∧ ∀ i, lin (R i) x ≤ 1}

def combinedNormal (R : Fin m → Fin d → ℝ) (weights : Fin m → ℝ) : Fin d → ℝ :=
  fun j => ∑ i, weights i * R i j

lemma combinedNormal_eval (R : Fin m → Fin d → ℝ) (weights : Fin m → ℝ)
    (x : Fin d → ℝ) :
    lin (combinedNormal R weights) x = ∑ i, weights i * lin (R i) x := by
  change (∑ j, (∑ i, weights i * R i j) * x j) =
    ∑ i, weights i * ∑ j, R i j * x j
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A nonnegative row combination yields the finite inverse-chart budget. -/
theorem weighted_sheared_budget
    (R : Fin m → Fin d → ℝ) (c : Fin d → ℝ) (weights : Fin m → ℝ)
    (hw : ∀ i, 0 ≤ weights i) (y : Fin d → ℝ)
    (hy : y ∈ orthantModel (fun i => R i + c)) :
    lin (combinedNormal R weights) y + (∑ i, weights i) * lin c y ≤
      ∑ i, weights i := by
  have h : ∀ i, weights i * (lin (R i) y + lin c y) ≤ weights i := by
    intro i
    have hi := hy.2 i
    rw [lin_add_apply] at hi
    simpa using mul_le_mul_of_nonneg_left hi (hw i)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => h i)
  simp_rw [mul_add] at hs
  rw [Finset.sum_add_distrib, ← combinedNormal_eval, ← Finset.sum_mul] at hs
  exact hs

/-- Strict inverse positivity follows from boundedness multipliers. The
transformed set has no spurious component on the far side of infinity. -/
theorem sheared_target_positive_domain
    (R : Fin m → Fin d → ℝ) (c : Fin d → ℝ) (weights : Fin m → ℝ)
    (hw : ∀ i, 0 ≤ weights i)
    (hmu : ∀ j, 0 < combinedNormal R weights j) :
    orthantModel (fun i => R i + c) ⊆ positiveDomain (-lin c) := by
  intro y hy
  have hbudget := weighted_sheared_budget R c weights hw y hy
  have hsigma : 0 ≤ ∑ i, weights i := Finset.sum_nonneg (fun i _ => hw i)
  have hmupos := lin_nonneg (combinedNormal R weights) y (fun j => (hmu j).le) hy.1
  change 0 < 1 + (-lin c) y
  simp only [LinearMap.neg_apply]
  by_contra hbad
  have hc : 1 ≤ lin c y := by linarith
  have hprod : (∑ i, weights i) ≤ (∑ i, weights i) * lin c y := by
    simpa using mul_le_mul_of_nonneg_left hc hsigma
  have hzero : lin (combinedNormal R weights) y = 0 := by linarith
  have hyzero : ∀ j, y j = 0 := by
    intro j
    have hsingle : combinedNormal R weights j * y j ≤
        lin (combinedNormal R weights) y := by
      exact Finset.single_le_sum
        (fun k _ => mul_nonneg (hmu k).le (hy.1 k)) (Finset.mem_univ j)
    rw [hzero] at hsingle
    have hp := hmu j
    have hn := hy.1 j
    nlinarith
  have hcy : lin c y = 0 := by simp [lin, hyzero]
  linarith

lemma orthant_source_positive_domain
    (R : Fin m → Fin d → ℝ) (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j) :
    orthantModel R ⊆ positiveDomain (lin c) := by
  intro x hx
  have h := lin_nonneg c x hc hx.1
  change 0 < 1 + lin c x
  linarith

lemma lin_perspective (a : Fin d → ℝ) (l : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (x : Fin d → ℝ) :
    lin a (perspective l x) = lin a x / denominator l x := by
  simp [perspective, map_smul, smul_eq_mul, div_eq_mul_inv, mul_comm]

lemma perspective_mem_sheared_orthant
    (R : Fin m → Fin d → ℝ) (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j)
    (x : Fin d → ℝ) (hx : x ∈ orthantModel R) :
    perspective (lin c) x ∈ orthantModel (fun i => R i + c) := by
  have hp := orthant_source_positive_domain R c hc hx
  refine ⟨?_, ?_⟩
  · intro j
    change (denominator (lin c) x)⁻¹ * x j ≥ 0
    exact mul_nonneg (inv_nonneg.mpr hp.le) (hx.1 j)
  · intro i
    rw [lin_perspective]
    apply (div_le_iff₀ hp).mpr
    rw [lin_add_apply]
    change lin (R i) x + lin c x ≤ 1 * (1 + lin c x)
    linarith [hx.2 i]

lemma inverse_mem_original_orthant
    (R : Fin m → Fin d → ℝ) (c : Fin d → ℝ) (weights : Fin m → ℝ)
    (hw : ∀ i, 0 ≤ weights i) (hmu : ∀ j, 0 < combinedNormal R weights j)
    (y : Fin d → ℝ) (hy : y ∈ orthantModel (fun i => R i + c)) :
    perspective (-lin c) y ∈ orthantModel R := by
  have hp := sheared_target_positive_domain R c weights hw hmu hy
  refine ⟨?_, ?_⟩
  · intro j
    change (denominator (-lin c) y)⁻¹ * y j ≥ 0
    exact mul_nonneg (inv_nonneg.mpr hp.le) (hy.1 j)
  · intro i
    rw [lin_perspective]
    apply (div_le_iff₀ hp).mpr
    have hi := hy.2 i
    rw [lin_add_apply] at hi
    change lin (R i) y ≤ 1 * (1 - lin c y)
    linarith

/-- Actual onto-set identity, not an assumed graph isomorphism. -/
theorem perspective_image_orthant_eq
    (R : Fin m → Fin d → ℝ) (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j)
    (weights : Fin m → ℝ) (hw : ∀ i, 0 ≤ weights i)
    (hmu : ∀ j, 0 < combinedNormal R weights j) :
    perspective (lin c) '' orthantModel R = orthantModel (fun i => R i + c) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact perspective_mem_sheared_orthant R c hc x hx
  · intro y hy
    have hp := sheared_target_positive_domain R c weights hw hmu hy
    refine ⟨perspective (-lin c) y,
      inverse_mem_original_orthant R c weights hw hmu y hy, ?_⟩
    simpa only [neg_neg] using perspective_inverse (-lin c) y (ne_of_gt hp)

/-- Every ordinary-edge budget is equivalent before and after normalization. -/
theorem orthant_diamLE_shear_iff
    (R : Fin m → Fin d → ℝ) (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j)
    (weights : Fin m → ℝ) (hw : ∀ i, 0 ≤ weights i)
    (hmu : ∀ j, 0 < combinedNormal R weights j) (B : ℕ) :
    DiamLE (orthantModel (fun i => R i + c)) B ↔ DiamLE (orthantModel R) B := by
  have himage := perspective_image_orthant_eq R c hc weights hw hmu
  have hsource := orthant_source_positive_domain R c hc
  have htarget := sheared_target_positive_domain R c weights hw hmu
  have hback : perspective (-lin c) '' orthantModel (fun i => R i + c) =
      orthantModel R := by
    apply Set.Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact inverse_mem_original_orthant R c weights hw hmu y hy
    · intro x hx
      refine ⟨perspective (lin c) x, perspective_mem_sheared_orthant R c hc x hx, ?_⟩
      exact perspective_inverse (lin c) x (ne_of_gt (hsource hx))
  constructor
  · intro hd
    have h := perspective_diamLE_image (-lin c) _ htarget B hd
    rwa [hback] at h
  · intro hd
    have h := perspective_diamLE_image (lin c) _ hsource B hd
    rwa [himage] at h

/-- After the scalar coordinate change y=K*z, all upper coefficients can
be arbitrarily close to one, while the preceding theorem preserves the graph.
This is an EXACT coefficient statement, not a numerical rank approximation. -/
theorem near_uniform_coefficients
    (R : Fin m → Fin d → ℝ) (M eta K : ℝ)
    (hM : ∀ i j, |R i j| ≤ M) (hK : 0 < K) (hgap : M < eta * K) :
    ∀ i j, 1 - eta < 1 + R i j / K ∧ 1 + R i j / K < 1 + eta := by
  intro i j
  have hr := abs_le.mp (hM i j)
  have hlo : -eta < R i j / K := (lt_div_iff₀ hK).mpr (by nlinarith)
  have hhi : R i j / K < eta := (div_lt_iff₀ hK).mpr (by linarith)
  constructor <;> linarith

#print axioms combinedNormal_eval
#print axioms weighted_sheared_budget
#print axioms sheared_target_positive_domain
#print axioms perspective_image_orthant_eq
#print axioms orthant_diamLE_shear_iff
#print axioms near_uniform_coefficients
end HirschPacking
