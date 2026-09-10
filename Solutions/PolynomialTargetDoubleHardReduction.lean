import Mathlib
import Definitions.Def_Hirsch_model
import Theorems.Thm_Hirsch_nonzero_supporting_row_of_distinct_extremes
import Solutions.PolynomialAccessPadding
import Solutions.PolynomialExcessTargetAccess

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschPolynomialAccess

/-- It is enough to solve existential target-facet access in the regime that
is simultaneously hard for ordinary Larman and for the excess-parameter
common-face bound.

The current platform child is stronger than this: it asks for an arbitrary
specified target facet.  The parent theorem only needs some target facet. -/
theorem full_target_access_of_double_hard_regime
    (hhard : ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hpoly a b) →
      ∀ u ∈ extremePoints ℝ (Hpoly a b),
      ∀ v ∈ extremePoints ℝ (Hpoly a b), u ≠ v →
      (∀ j, a j ≠ 0 → ⟪a j, u⟫ ≠ b j ∨ ⟪a j, v⟫ ≠ b j) →
      n < 2 ^ (d - 3) →
      n < 2 ^ ((n - 2 * d) - 3) →
      ∃ (i : Fin n) (z : EuclideanSpace ℝ (Fin d)),
        a i ≠ 0 ∧ ⟪a i, v⟫ = b i ∧
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
      ∃ (i : Fin n) (z : EuclideanSpace ℝ (Fin d)),
        a i ≠ 0 ∧ ⟪a i, v⟫ = b i ∧
        z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
        ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
          w 0 = u ∧ w (C * (n + d) ^ k) = z ∧
          ∀ j < C * (n + d) ^ k,
            w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  obtain ⟨C, k, hhard⟩ := hhard
  let C' : ℕ := C + 2
  let k' : ℕ := k + 2
  refine ⟨C', k', ?_⟩
  intro d n a b hbd u hu v hv huv hsep
  have hdpos : 0 < d := by
    by_contra hd
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    subst d
    exact huv (Subsingleton.elim _ _)
  have hN : 1 ≤ n + d := by omega
  have hpow2 : (n + d) ^ 2 ≤ (n + d) ^ k' := by
    dsimp [k']
    have h := nat_pow_le_pow_add (n + d) 2 k hN
    simpa [Nat.add_comm] using h
  have hcoef1 : 1 ≤ C' := by simp [C']
  have hcoef2 : 2 ≤ C' := by simp [C']
  by_cases hambient : 2 ^ (d - 3) ≤ n
  · obtain ⟨i, hai, hiv⟩ :=
      Hirsch.nonzero_supporting_row_of_distinct_extremes d n a b hbd u hu v hv huv
    obtain ⟨z, hz, hiz, w, hw0, hwB, hwstep⟩ :=
      larman_easy_regime_given_face_access d n a b hbd hu hv hambient i hiv
    have hbudget : (n + d) ^ 2 ≤ C' * (n + d) ^ k' :=
      hpow2.trans (Nat.le_mul_of_pos_left _ (by omega))
    obtain ⟨w', hw'0, hw'B, hw'step⟩ :=
      pad_walk (Adj (Hpoly a b)) hbudget w hw0 hwB hwstep
    exact ⟨i, z, hai, hiv, hz, hiz, w', hw'0, hw'B, hw'step⟩
  · have hambientHard : n < 2 ^ (d - 3) := by omega
    by_cases hexcess : 2 ^ ((n - 2 * d) - 3) ≤ n
    · obtain ⟨i, z, hai, hiv, hz, hiz, w, hw0, hwB, hwstep⟩ :=
        target_facet_access_excess_bound a b hbd u v hu hv huv hsep
      let E := 2 ^ ((n - 2 * d) - 3)
      let B := n * E + 1
      have hmul : n * E ≤ n * n := Nat.mul_le_mul_left n hexcess
      have hn2 : n * n ≤ (n + d) ^ 2 := by
        simp [pow_two]
        nlinarith
      have hone : 1 ≤ (n + d) ^ 2 := one_le_pow₀ hN
      have hB2 : B ≤ 2 * (n + d) ^ 2 := by
        dsimp [B, E]
        calc
          n * 2 ^ ((n - 2 * d) - 3) + 1 ≤ n * n + 1 :=
            Nat.add_le_add_right hmul 1
          _ ≤ (n + d) ^ 2 + (n + d) ^ 2 := Nat.add_le_add hn2 hone
          _ = 2 * (n + d) ^ 2 := by ring
      have h2final : 2 * (n + d) ^ 2 ≤ C' * (n + d) ^ k' :=
        Nat.mul_le_mul hcoef2 hpow2
      have hbudget : B ≤ C' * (n + d) ^ k' := hB2.trans h2final
      obtain ⟨w', hw'0, hw'B, hw'step⟩ :=
        pad_walk (Adj (Hpoly a b)) hbudget w hw0 hwB hwstep
      exact ⟨i, z, hai, hiv, hz, hiz, w', hw'0, hw'B, hw'step⟩
    · have hexcessHard : n < 2 ^ ((n - 2 * d) - 3) := by omega
      obtain ⟨i, z, hai, hiv, hz, hiz, w, hw0, hwB, hwstep⟩ :=
        hhard d n a b hbd u hu v hv huv hsep hambientHard hexcessHard
      have hpow : (n + d) ^ k ≤ (n + d) ^ k' := by
        dsimp [k']
        exact nat_pow_le_pow_add (n + d) k 2 hN
      have hC : C ≤ C' := by simp [C']
      have hbudget : C * (n + d) ^ k ≤ C' * (n + d) ^ k' :=
        Nat.mul_le_mul hC hpow
      obtain ⟨w', hw'0, hw'B, hw'step⟩ :=
        pad_walk (Adj (Hpoly a b)) hbudget w hw0 hwB hwstep
      exact ⟨i, z, hai, hiv, hz, hiz, w', hw'0, hw'B, hw'step⟩

end HirschPolynomialAccess
