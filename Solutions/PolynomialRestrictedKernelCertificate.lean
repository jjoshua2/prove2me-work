import Mathlib

/-!
# Finite row-reduction certificates for a one-ray restricted kernel

An exact RREF checker can certify a candidate support without quantifying over
all null vectors: for each supported coordinate, give a row combination whose
values on the standard columns recover that coordinate relative to one fixed
pivot coordinate. Linearity promotes those finitely many column identities to
all vectors, and any null vector supported inside the candidate support is then
a scalar multiple of the candidate.

This is a certificate interface. It does not formalize an imperative Gaussian
elimination program or claim that a particular program produced the witnesses.
-/
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace Hirsch

/-- Exact row-combination identities checked on the coordinate columns imply
that the signed kernel restricted to the support of `x` is the one-dimensional
ray/line spanned by `x`. -/
theorem rref_basis_certificate_restricted_kernel_one_ray
    (n k : ℕ) (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ))
    (x : Fin n → ℝ) (j : Fin n) (dual : Fin n → Fin k → ℝ)
    (hxj : x j ≠ 0)
    (hcol : ∀ i, x i ≠ 0 → ∀ l : Fin n,
      (∑ r, dual i r * (A (fun q => if l = q then (1 : ℝ) else 0)) r) =
        (if l = i then 1 else 0) -
          (x i / x j) * (if l = j then 1 else 0)) :
    ∀ z : Fin n → ℝ, A z = 0 →
      Function.support z ⊆ Function.support x → ∃ t : ℝ, z = t • x := by
  classical
  have hdual : ∀ i, x i ≠ 0 → ∀ z : Fin n → ℝ,
      (∑ r, dual i r * (A z) r) = z i - (x i / x j) * z j := by
    intro i hxi z
    have heval : ∀ r : Fin k, (A z) r =
        ∑ l, z l * (A (fun q => if l = q then (1 : ℝ) else 0)) r := by
      intro r
      rw [A.pi_apply_eq_sum_univ z]
      simp
    calc
      (∑ r, dual i r * (A z) r) =
          ∑ r, dual i r *
            (∑ l, z l * (A (fun q => if l = q then (1 : ℝ) else 0)) r) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [heval r]
      _ = ∑ r, ∑ l, dual i r *
            (z l * (A (fun q => if l = q then (1 : ℝ) else 0)) r) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
      _ = ∑ l, ∑ r, dual i r *
            (z l * (A (fun q => if l = q then (1 : ℝ) else 0)) r) := by
        rw [Finset.sum_comm]
      _ = ∑ l, z l *
            (∑ r, dual i r *
              (A (fun q => if l = q then (1 : ℝ) else 0)) r) := by
        apply Finset.sum_congr rfl
        intro l _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ = ∑ l, z l *
            ((if l = i then 1 else 0) -
              (x i / x j) * (if l = j then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro l _
        rw [hcol i hxi l]
      _ = z i - (x i / x j) * z j := by
        simp [mul_sub, Finset.sum_sub_distrib]
  intro z hz hzx
  refine ⟨z j / x j, ?_⟩
  funext i
  change z i = (z j / x j) * x i
  by_cases hxi : x i = 0
  · have hzi : z i = 0 := by
      by_contra hzi
      exact (hzx hzi) hxi
    simp [hzi, hxi]
  · have hi := hdual i hxi z
    rw [hz] at hi
    simp at hi
    have hiz : z i = (x i / x j) * z j := by linarith
    rw [hiz, div_eq_mul_inv, div_eq_mul_inv]
    ring

#print axioms rref_basis_certificate_restricted_kernel_one_ray
end Hirsch
