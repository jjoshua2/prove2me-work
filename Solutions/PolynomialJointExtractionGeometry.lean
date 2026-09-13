import Mathlib

/-!
# Exact joint extraction is a packing region, not an order-independent box

The complete circuit proof gives nonnegative joint scale coefficients. These
finite lemmas record convexity, downward closure, a separating row for an
inadmissible simultaneous choice, and the concrete competing-unit-capacity
example. They do not claim that the circuit-to-geometry implication is already
formalized. NEW UNCOMPILED candidates.
-/
open Set
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace HirschJointExtraction
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def ScaleRegion (Γ : κ → ι → ℝ) (b : κ → ℝ) : Set (ι → ℝ) :=
  {t | (∀ i, 0 ≤ t i) ∧ ∀ j, (∑ i, Γ j i*t i) ≤ b j}

theorem scaleRegion_convex (Γ : κ → ι → ℝ) (b : κ → ℝ) :
    Convex ℝ (ScaleRegion Γ b) := by
  intro x hx y hy s t hs ht hst
  constructor
  · intro i
    change 0 ≤ s*x i+t*y i
    exact add_nonneg (mul_nonneg hs (hx.1 i)) (mul_nonneg ht (hy.1 i))
  · intro j
    have h₁ := mul_le_mul_of_nonneg_left (hx.2 j) hs
    have h₂ := mul_le_mul_of_nonneg_left (hy.2 j) ht
    have he : (∑ i, Γ j i*(s*x i+t*y i)) =
        s*(∑ i, Γ j i*x i)+t*(∑ i, Γ j i*y i) := by
      rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    change (∑ i, Γ j i*(s*x i+t*y i)) ≤ b j
    rw [he]
    nlinarith

theorem scaleRegion_downward (Γ : κ → ι → ℝ) (b : κ → ℝ)
    (hΓ : ∀ j i, 0 ≤ Γ j i) {s t : ι → ℝ}
    (ht : t ∈ ScaleRegion Γ b) (hs : ∀ i, 0 ≤ s i)
    (hst : ∀ i, s i ≤ t i) : s ∈ ScaleRegion Γ b := by
  refine ⟨hs,fun j => ?_⟩
  calc
    (∑ i, Γ j i*s i) ≤ ∑ i, Γ j i*t i :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hst i) (hΓ j i))
    _ ≤ b j := ht.2 j

theorem violating_row_excludes_scales (Γ : κ → ι → ℝ) (b : κ → ℝ)
    (t : ι → ℝ) (j : κ) (h : b j < ∑ i, Γ j i*t i) :
    t ∉ ScaleRegion Γ b := by
  intro ht
  exact (not_lt_of_ge (ht.2 j)) h

/-- Separate unit capacities do not imply simultaneous admissibility. -/
theorem competing_unit_capacities :
    (0 : ℝ)+1 ≤ 1 ∧ (1 : ℝ)+0 ≤ 1 ∧ ¬ (1 : ℝ)+1 ≤ 1 := by norm_num

/-- Monotone support choices on one objective interval visit at most v states.
This is the finite count used in the classical vertex-sensitive route lift. -/
theorem vertex_sensitive_lift_budget (L v changes cost : ℕ)
    (hv : 1 ≤ v) (hc : changes ≤ (L+1)*(v-1))
    (hcost : cost ≤ L+changes) : cost+1 ≤ (L+1)*v := by
  have he : v-1+1=v := Nat.sub_add_cancel hv
  nlinarith

#print axioms scaleRegion_convex
#print axioms scaleRegion_downward
#print axioms violating_row_excludes_scales
#print axioms competing_unit_capacities
#print axioms vertex_sensitive_lift_budget
end HirschJointExtraction
