import Mathlib
import Definitions.Def_Hirsch_model
import Theorems.Thm_Hirsch_larman_bound
import Solutions.PolynomialAccessPadding
import Solutions.PolynomialSeparatedRows

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 3000000

namespace HirschPolynomialAccess

/-- A substantive reduction of the remaining polynomial-Hirsch leaf.

It is enough to prove polynomial specified-face access only when the two
separated extreme points force `2*d ≤ n` and Larman's exponential factor is
still larger than `n`, i.e. `n < 2^(d-3)`.  Outside that regime Larman is
already quadratic. -/
theorem full_access_of_hard_regime
    (hhard : ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hpoly a b) →
      ∀ u ∈ extremePoints ℝ (Hpoly a b),
      ∀ v ∈ extremePoints ℝ (Hpoly a b), u ≠ v →
      (∀ j, a j ≠ 0 → ⟪a j, u⟫ ≠ b j ∨ ⟪a j, v⟫ ≠ b j) →
      2 * d ≤ n → n < 2 ^ (d - 3) →
      ∀ i : Fin n, a i ≠ 0 → ⟪a i, v⟫ = b i →
      ∃ z : EuclideanSpace ℝ (Fin d),
        z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
        ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
          w 0 = u ∧ w (C * (n + d) ^ k) = z ∧
          ∀ j < C * (n + d) ^ k,
            w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1))) :
    ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hpoly a b) →
      ∀ u ∈ extremePoints ℝ (Hpoly a b),
      ∀ v ∈ extremePoints ℝ (Hpoly a b), u ≠ v →
      (∀ j, a j ≠ 0 → ⟪a j, u⟫ ≠ b j ∨ ⟪a j, v⟫ ≠ b j) →
      ∀ i : Fin n, a i ≠ 0 → ⟪a i, v⟫ = b i →
      ∃ z : EuclideanSpace ℝ (Fin d),
        z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
        ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
          w 0 = u ∧ w (C * (n + d) ^ k) = z ∧
          ∀ j < C * (n + d) ^ k,
            w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  obtain ⟨C, k, hhard⟩ := hhard
  let C' : ℕ := C + 1
  let k' : ℕ := k + 2
  refine ⟨C', k', ?_⟩
  intro d n a b hbd u hu v hv huv hsep i hai hiv
  have hdpos : 0 < d := by
    by_contra hd
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    subst d
    apply hai
    exact Subsingleton.elim _ _
  have hN : 1 ≤ n + d := by omega
  have h2d : 2 * d ≤ n :=
    separated_extremes_n_ge_two_d a b u v hu hv hsep
  by_cases hreg : 2 ^ (d - 3) ≤ n
  · have hne : (Hpoly a b).Nonempty := ⟨u, hu.1⟩
    have hL : DiamLE (Hpoly a b) (n * 2 ^ (d - 3)) :=
      Hirsch.larman_bound d n a b hne hbd
    have hLquad : n * 2 ^ (d - 3) ≤ (n + d) ^ 2 := by
      have h1 : n * 2 ^ (d - 3) ≤ n * n := Nat.mul_le_mul_left n hreg
      have h2 : n * n ≤ (n + d) ^ 2 := by
        simp [pow_two]
        nlinarith
      exact h1.trans h2
    have hpow : (n + d) ^ 2 ≤ (n + d) ^ (k + 2) := by
      have h := nat_pow_le_pow_add (n + d) 2 k hN
      simpa [Nat.add_comm] using h
    have hcoef : (n + d) ^ (k + 2) ≤ C' * (n + d) ^ (k + 2) := by
      have hC : 1 ≤ C' := by simp [C']
      have h := Nat.mul_le_mul_right ((n + d) ^ (k + 2)) hC
      simpa using h
    have hbudget : n * 2 ^ (d - 3) ≤ C' * (n + d) ^ k' := by
      dsimp [k']
      exact hLquad.trans (hpow.trans hcoef)
    exact given_face_access_of_diamLE a b hu hv
      (diamLE_mono (Hpoly a b) hbudget hL) i hiv
  · have hhardreg : n < 2 ^ (d - 3) := by omega
    obtain ⟨z, hz, hiz, w, hw0, hwB, hwstep⟩ :=
      hhard d n a b hbd u hu v hv huv hsep h2d hhardreg i hai hiv
    have hpow : (n + d) ^ k ≤ (n + d) ^ (k + 2) :=
      nat_pow_le_pow_add (n + d) k 2 hN
    have hC : C ≤ C' := by simp [C']
    have hbudget : C * (n + d) ^ k ≤ C' * (n + d) ^ k' := by
      dsimp [k']
      exact Nat.mul_le_mul hC hpow
    obtain ⟨w', hw'0, hw'B, hw'step⟩ :=
      pad_walk (Adj (Hpoly a b)) hbudget w hw0 hwB hwstep
    exact ⟨z, hz, hiz, w', hw'0, hw'B, hw'step⟩

end HirschPolynomialAccess
