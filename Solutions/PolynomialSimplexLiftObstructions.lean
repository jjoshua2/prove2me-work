import Mathlib

/-!
# Simplex removal: exact lift equations and small dual obstructions

For Q=conv(0,g_1,...,g_k), translation into its erosion is a feasibility
problem in k variables, even when the original polytope has large dimension.
This file proves the exact set-membership reduction, erosion inclusion, and
the dual scalar certificate. The complete positive-circuit generation theorem
and the sufficiency direction of Farkas are written in the accompanying note;
they are NOT assumed as a new axiom or claimed formalized by these cores.

NEW UNCOMPILED candidates. No platform acceptance is asserted.
-/
open Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HirschSimplexRemoval

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def coefficients (t : ℝ) (z : κ → ℝ) : Prop :=
  (∀ j, 0 ≤ z j) ∧ (∑ j, z j) ≤ t

def combination (g : κ → E) (z : κ → ℝ) : E :=
  ∑ j, z j • g j

def halfspaces (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) : Set E :=
  {x | ∀ i, a i x ≤ b i}

def eroded (a : ι → E →ₗ[ℝ] ℝ) (b h : ι → ℝ) (t : ℝ) : Set E :=
  halfspaces a (fun i => b i-t*h i)

def simplexSum (P : Set E) (g : κ → E) (t : ℝ) : Set E :=
  {x | ∃ p ∈ P, ∃ z : κ → ℝ, coefficients t z ∧ x=p+combination g z}

lemma apply_combination (a : E →ₗ[ℝ] ℝ) (g : κ → E) (z : κ → ℝ) :
    a (combination g z) = ∑ j, z j * a (g j) := by
  simp [combination, map_sum, map_smul]

/-- The exact lifted feasibility system, not merely a containment test. -/
theorem mem_eroded_simplexSum_iff
    (a : ι → E →ₗ[ℝ] ℝ) (b h : ι → ℝ) (g : κ → E) (t : ℝ) (x : E) :
    x ∈ simplexSum (eroded a b h t) g t ↔
      ∃ z : κ → ℝ, coefficients t z ∧
        ∀ i, -(∑ j, z j*a i (g j)) ≤ b i-a i x-t*h i := by
  constructor
  · rintro ⟨p,hp,z,hz,hx⟩
    refine ⟨z,hz,?_⟩
    intro i
    have he := congrArg (fun w : E => a i w) hx
    rw [map_add,apply_combination] at he
    have hi := hp i
    linarith
  · rintro ⟨z,hz,hi⟩
    refine ⟨x-combination g z,?_,z,hz,?_⟩
    · intro i
      simp only [map_sub,apply_combination]
      have h := hi i
      linarith
    · abel

/-- Valid support values always give the erosion-plus-simplex inclusion.
The reverse inclusion needs the complete dual-feasibility argument. -/
theorem eroded_simplexSum_subset
    (a : ι → E →ₗ[ℝ] ℝ) (b h : ι → ℝ) (g : κ → E) (t : ℝ)
    (hnon : ∀ i, 0 ≤ h i) (hsupport : ∀ i j, a i (g j) ≤ h i) :
    simplexSum (eroded a b h t) g t ⊆ halfspaces a b := by
  rintro x ⟨p,hp,z,hz,hx⟩ i
  have hs : (∑ j, z j*a i (g j)) ≤ (∑ j, z j)*h i := by
    calc
      (∑ j, z j*a i (g j)) ≤ ∑ j, z j*h i :=
        Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_left (hsupport i j) (hz.1 j))
      _ = (∑ j, z j)*h i := by rw [Finset.sum_mul]
  have ht := mul_le_mul_of_nonneg_right hz.2 (hnon i)
  have hi := hp i
  rw [hx,map_add,apply_combination]
  linarith

/-- Finite signed elimination identity. In the application V_ij=a_i(g_j)
and R_i=b_i-a_i(x). All columns are bounded by gamma. -/
theorem simplex_obstruction_bound
    (V : ι → κ → ℝ) (R h λ : ι → ℝ) (z : κ → ℝ) (t γ : ℝ)
    (hλ : ∀ i, 0 ≤ λ i) (hz : coefficients t z) (hγ : 0 ≤ γ)
    (hcol : ∀ j, (∑ i, λ i*V i j) ≤ γ)
    (hlift : ∀ i, t*h i-R i ≤ ∑ j, z j*V i j) :
    t*((∑ i, λ i*h i)-γ) ≤ ∑ i, λ i*R i := by
  have hs : (∑ i, λ i*(t*h i-R i)) ≤
      ∑ i, λ i*(∑ j, z j*V i j) :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hlift i) (hλ i))
  have he : (∑ i, λ i*(∑ j, z j*V i j)) =
      ∑ j, z j*(∑ i, λ i*V i j) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hu : (∑ j, z j*(∑ i, λ i*V i j)) ≤ (∑ j, z j)*γ := by
    calc
      _ ≤ ∑ j, z j*γ :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hcol j) (hz.1 j))
      _ = _ := by rw [Finset.sum_mul]
  have ht := mul_le_mul_of_nonneg_right hz.2 hγ
  have hl : (∑ i, λ i*(t*h i-R i)) =
      t*(∑ i, λ i*h i)-(∑ i, λ i*R i) := by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,hl] at hs
  nlinarith

/-- A sharp positive-demand obstruction rules out every larger lifted amount.
The point witnessing this inequality belongs to the original H-polytope. -/
theorem sharp_obstruction_maximal (cost demand capacity amount : ℝ)
    (hd : 0 < demand) (hsharp : cost=capacity*demand)
    (hnecessary : amount*demand ≤ cost) : amount ≤ capacity := by
  rw [hsharp] at hnecessary
  exact (mul_le_mul_right hd).mp hnecessary

/-- Negative pairing with a nonnegative kernel vector forbids feasibility.
These vectors are algebraic elimination circuits, NOT polytope circuit walks. -/
theorem no_lift_of_negative_kernel
    {J : Type*} [Fintype J]
    (C : J → E →ₗ[ℝ] ℝ) (rhs w : J → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hzero : (∑ j, w j • C j)=0)
    (hneg : (∑ j, w j*rhs j)<0) :
    ¬ ∃ x : E, ∀ j, C j x ≤ rhs j := by
  rintro ⟨x,hx⟩
  have hs : (∑ j, w j*C j x) ≤ ∑ j, w j*rhs j :=
    Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hx j) (hw j))
  have he := congrArg (fun f : E →ₗ[ℝ] ℝ => f x) hzero
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,
    LinearMap.zero_apply] at he
  linarith

#print axioms apply_combination
#print axioms mem_eroded_simplexSum_iff
#print axioms eroded_simplexSum_subset
#print axioms simplex_obstruction_bound
#print axioms sharp_obstruction_maximal
#print axioms no_lift_of_negative_kernel
end HirschSimplexRemoval
