import Solutions.PolynomialPositivePerspective
import Solutions.PolynomialRowBlockRouting

/-!
# Routing products hidden by a positive projective chart

An exact rank-one row shear A_i |-> A_i + b_i*c preserves the graph when
both projective denominators are positive on their feasible sets. This extends
the existing affine row-block criterion to examples with a connected normal
matroid and arbitrarily large shortest-repair support deficit.

All hypotheses are explicit. No claim is made that arbitrary carriers admit
such a chart. Verification receipts are maintained separately.
-/
open Set Hirsch HirschPerspective
open scoped BigOperators RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace HirschProjectiveBlocks

variable {d n : ℕ}

def rowFunctional (c : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ where
  toFun x := ⟪c, x⟫
  map_add' x y := by simp [inner_add_right]
  map_smul' r x := by simp [inner_smul_right]

lemma rowFunctional_neg (c : EuclideanSpace ℝ (Fin d)) :
    rowFunctional (-c) = -rowFunctional c := by
  ext x
  simp [rowFunctional, inner_neg_left]

def shearRows (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (c : EuclideanSpace ℝ (Fin d)) :
    Fin n → EuclideanSpace ℝ (Fin d) := fun i => a i + b i • c

lemma shearRows_inverse (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (c : EuclideanSpace ℝ (Fin d)) :
    shearRows (shearRows a b c) b (-c) = a := by
  funext i
  simp [shearRows, smul_neg, add_assoc]

/-- Exact slack scaling. Its positive divisor is essential to feasibility. -/
theorem shear_slack_identity (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (c x : EuclideanSpace ℝ (Fin d))
    (hx : denominator (rowFunctional c) x ≠ 0) (i : Fin n) :
    b i - ⟪shearRows a b c i, perspective (rowFunctional c) x⟫ =
      (b i - ⟪a i, x⟫) / denominator (rowFunctional c) x := by
  have hd : 1 + ⟪c, x⟫ ≠ 0 := hx
  simp [shearRows, perspective, denominator, rowFunctional,
    inner_add_left, inner_smul_left, inner_smul_right, div_eq_mul_inv]
  field_simp [hd]
  ring

lemma perspective_mem_sheared_hpoly (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (c x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ Hpoly a b) (hpos : x ∈ positiveDomain (rowFunctional c)) :
    perspective (rowFunctional c) x ∈ Hpoly (shearRows a b c) b := by
  intro i
  have hs : 0 ≤ b i - ⟪shearRows a b c i, perspective (rowFunctional c) x⟫ := by
    rw [shear_slack_identity a b c x (ne_of_gt hpos) i]
    exact div_nonneg (sub_nonneg.mpr (hx i)) (le_of_lt hpos)
  exact sub_nonneg.mp hs

/-- No missing halfspace is silently discarded: source and target positivity
are both supplied. They can be certified by nonnegative row multipliers. -/
theorem perspective_image_hpoly_eq_shear
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (c : EuclideanSpace ℝ (Fin d))
    (hsource : Hpoly a b ⊆ positiveDomain (rowFunctional c))
    (htarget : Hpoly (shearRows a b c) b ⊆ positiveDomain (-rowFunctional c)) :
    perspective (rowFunctional c) '' Hpoly a b = Hpoly (shearRows a b c) b := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact perspective_mem_sheared_hpoly a b c x hx (hsource hx)
  · intro y hy
    have hp : y ∈ positiveDomain (rowFunctional (-c)) := by
      rw [rowFunctional_neg]
      exact htarget hy
    have hpre := perspective_mem_sheared_hpoly (shearRows a b c) b (-c) y hy hp
    rw [shearRows_inverse, rowFunctional_neg] at hpre
    refine ⟨perspective (-rowFunctional c) y, hpre, ?_⟩
    simpa only [neg_neg] using
      perspective_inverse (-rowFunctional c) y (ne_of_gt (htarget hy))

/-- Transport an arbitrary known graph bound through a certified row shear. -/
theorem hpoly_diamLE_of_positive_shear
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (B : ℕ)
    (hsource : Hpoly a b ⊆ positiveDomain (rowFunctional c))
    (htarget : Hpoly (shearRows a b c) b ⊆ positiveDomain (-rowFunctional c))
    (hdiam : DiamLE (Hpoly a b) B) :
    DiamLE (Hpoly (shearRows a b c) b) B := by
  have hr := perspective_diamLE_image (rowFunctional c) (Hpoly a b) hsource B hdiam
  rwa [perspective_image_hpoly_eq_shear a b c hsource htarget] at hr

/-- A checkable Farkas-style sufficient certificate for denominator positivity.
The represented normal is -c, and the weighted upper bound is strictly below 1. -/
theorem positiveDomain_of_row_multipliers
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (weights : Fin n → ℝ)
    (hweights : ∀ i, 0 ≤ weights i)
    (hnormal : (∑ i, weights i • a i) = -c)
    (hmargin : (∑ i, weights i * b i) < 1) :
    Hpoly a b ⊆ positiveDomain (rowFunctional c) := by
  intro x hx
  have hsum : (∑ i, weights i * ⟪a i, x⟫) ≤ ∑ i, weights i * b i :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hx i) (hweights i))
  have heq : (∑ i, weights i * ⟪a i, x⟫) = -⟪c, x⟫ := by
    calc
      (∑ i, weights i * ⟪a i, x⟫) = ⟪∑ i, weights i • a i, x⟫ := by
        simp [sum_inner, inner_smul_left]
      _ = -⟪c, x⟫ := by rw [hnormal]; simp
  rw [heq] at hsum
  change 0 < 1 + ⟪c, x⟫
  linarith

/-- Consume both finite denominator certificates and transport a known bound.
The hypotheses are identities and inequalities in the describing rows, without
quantification over all feasible points or an assumed chart isomorphism. -/
theorem hpoly_diamLE_of_shear_multipliers
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (weights inverseWeights : Fin n → ℝ)
    (hweights : ∀ i, 0 ≤ weights i)
    (hnormal : (∑ i, weights i • a i) = -c)
    (hmargin : (∑ i, weights i * b i) < 1)
    (hinverseWeights : ∀ i, 0 ≤ inverseWeights i)
    (hinverseNormal : (∑ i, inverseWeights i • (a i + b i • c)) = c)
    (hinverseMargin : (∑ i, inverseWeights i * b i) < 1)
    (B : ℕ) (hdiam : DiamLE (Hpoly a b) B) :
    DiamLE (Hpoly (fun i => a i + b i • c) b) B := by
  have hsource := positiveDomain_of_row_multipliers a b c weights hweights hnormal hmargin
  have htarget : Hpoly (shearRows a b c) b ⊆ positiveDomain (-rowFunctional c) := by
    rw [← rowFunctional_neg]
    exact positiveDomain_of_row_multipliers (shearRows a b c) b (-c) inverseWeights
      hinverseWeights (by simpa only [neg_neg] using hinverseNormal) hinverseMargin
  exact hpoly_diamLE_of_positive_shear a b c B hsource htarget hdiam

/-- Final sufficient routing criterion. The actual input normals may be
inseparable into linear blocks; only their certified projective unshearing
must have the existing independent small-excess blocks. Total excess and
number of factors are unrestricted. -/
theorem hpoly_diamLE_excess_of_projectively_hidden_small_row_blocks
    (hsmall : ∀ {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
      (b : Fin n → ℝ), Bornology.IsBounded (Hpoly a b) →
      n ≤ d + 3 → DiamLE (Hpoly a b) (n - d))
    {k : ℕ} (dims counts : Fin k → ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ]
      (∀ i : Fin k, EuclideanSpace ℝ (Fin (dims i))))
    (e : (Σ i : Fin k, Fin (counts i)) ≃ Fin n)
    (A : ∀ i : Fin k, Fin (counts i) → EuclideanSpace ℝ (Fin (dims i)))
    (hrows : ∀ z i j, ⟪a (e ⟨i, j⟩), T.symm z⟫ = ⟪A i j, z i⟫)
    (hbd : Bornology.IsBounded (Hpoly a b)) (hne : (Hpoly a b).Nonempty)
    (hcount : ∀ i, dims i ≤ counts i)
    (hsmallcount : ∀ i, counts i ≤ dims i + 3)
    (c : EuclideanSpace ℝ (Fin d))
    (hsource : Hpoly a b ⊆ positiveDomain (rowFunctional c))
    (htarget : Hpoly (shearRows a b c) b ⊆ positiveDomain (-rowFunctional c)) :
    DiamLE (Hpoly (shearRows a b c) b) (n - d) := by
  apply hpoly_diamLE_of_positive_shear a b c (n-d) hsource htarget
  exact HirschRowBlocks.hpoly_diamLE_excess_of_small_row_blocks
    hsmall dims counts a b T e A hrows hbd hne hcount hsmallcount

#print axioms shear_slack_identity
#print axioms perspective_image_hpoly_eq_shear
#print axioms hpoly_diamLE_of_positive_shear
#print axioms positiveDomain_of_row_multipliers
#print axioms hpoly_diamLE_of_shear_multipliers
#print axioms hpoly_diamLE_excess_of_projectively_hidden_small_row_blocks
end HirschProjectiveBlocks
