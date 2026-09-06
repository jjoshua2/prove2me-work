import Mathlib
import Definitions.Def_Hirsch_model
import Theorems.Thm_Hirsch_larman_bound
import Theorems.Thm_Hirsch_nonzero_supporting_row_of_distinct_extremes
import Solutions.PolynomialFaceAccessBench
import Solutions.PolynomialAccessPadding
import Solutions.PolynomialSeparatedRows
import Solutions.PolynomialBalancedOneStep

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschPolynomialAccess

/-- A sharper reduction for the theorem the parent actually needs.

Unlike the current platform leaf, this hypothesis asks only for access to
*some* target facet, and only in the strict hard regime
`2*d < n < 2^(d-3)`.  The boundary `n=2d` is one edge by
`balanced_separated_some_target_facet_one_step`, while the opposite regime is
quadratic by Larman. -/
theorem full_target_access_of_strict_hard_regime
    (hhard : ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hpoly a b) →
      ∀ u ∈ extremePoints ℝ (Hpoly a b),
      ∀ v ∈ extremePoints ℝ (Hpoly a b), u ≠ v →
      (∀ j, a j ≠ 0 → ⟪a j, u⟫ ≠ b j ∨ ⟪a j, v⟫ ≠ b j) →
      2 * d < n → n < 2 ^ (d - 3) →
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
  let C' : ℕ := C + 1
  let k' : ℕ := k + 2
  refine ⟨C', k', ?_⟩
  intro d n a b hbd u hu v hv huv hsep
  have hdpos : 0 < d := by
    by_contra hd
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    subst d
    exact huv (Subsingleton.elim _ _)
  have hN : 1 ≤ n + d := by omega
  have h2d : 2 * d ≤ n :=
    separated_extremes_n_ge_two_d a b u v hu hv hsep
  by_cases heq : n = 2 * d
  · subst n
    obtain ⟨i, z, hai, hiv, hz, hiz, huz⟩ :=
      balanced_separated_some_target_facet_one_step d a b hbd u v hu hv huv hsep
    let w1 : ℕ → EuclideanSpace ℝ (Fin d) := fun j => if j = 0 then u else z
    have hw10 : w1 0 = u := by simp [w1]
    have hw11 : w1 1 = z := by simp [w1]
    have hw1step : ∀ j < 1,
        w1 j = w1 (j + 1) ∨ Adj (Hpoly a b) (w1 j) (w1 (j + 1)) := by
      intro j hj
      have hj0 : j = 0 := by omega
      subst j
      simp [w1, huz]
    have hpow1 : 1 ≤ (2 * d + d) ^ k' := one_le_pow₀ (by omega)
    have hC1 : 1 ≤ C' := by simp [C']
    have hbudget : 1 ≤ C' * (2 * d + d) ^ k' := by
      exact le_trans hpow1 (Nat.le_mul_of_pos_left _ (by omega))
    obtain ⟨w, hw0, hwB, hwstep⟩ :=
      pad_walk (Adj (Hpoly a b)) hbudget w1 hw10 hw11 hw1step
    exact ⟨i, z, hai, hiv, hz, hiz, w, hw0, hwB, hwstep⟩
  · have hstrict2d : 2 * d < n := by omega
    by_cases hreg : 2 ^ (d - 3) ≤ n
    · obtain ⟨i, hai, hiv⟩ :=
        Hirsch.nonzero_supporting_row_of_distinct_extremes d n a b hbd u hu v hv huv
      have hne : (Hpoly a b).Nonempty := ⟨u, hu.1⟩
      have hL : DiamLE (Hpoly a b) (n * 2 ^ (d - 3)) :=
        Hirsch.larman_bound d n a b hne hbd
      have hquad : n * 2 ^ (d - 3) ≤ (n + d) ^ 2 := by
        have h1 : n * 2 ^ (d - 3) ≤ n * n := Nat.mul_le_mul_left n hreg
        have h2 : n * n ≤ (n + d) ^ 2 := by
          simp [pow_two]
          nlinarith
        exact h1.trans h2
      have hpow : (n + d) ^ 2 ≤ (n + d) ^ k' := by
        dsimp [k']
        have h := nat_pow_le_pow_add (n + d) 2 k hN
        simpa [Nat.add_comm] using h
      have hcoef : (n + d) ^ k' ≤ C' * (n + d) ^ k' := by
        have hC : 1 ≤ C' := by simp [C']
        exact Nat.le_mul_of_pos_left _ (by omega)
      have hbudget : n * 2 ^ (d - 3) ≤ C' * (n + d) ^ k' :=
        hquad.trans (hpow.trans hcoef)
      obtain ⟨z, hz, hiz, w, hw0, hwB, hwstep⟩ :=
        given_face_access_of_diamLE a b hu hv
          (diamLE_mono (Hpoly a b) hbudget hL) i hiv
      exact ⟨i, z, hai, hiv, hz, hiz, w, hw0, hwB, hwstep⟩
    · have hhardreg : n < 2 ^ (d - 3) := by omega
      obtain ⟨i, z, hai, hiv, hz, hiz, w, hw0, hwB, hwstep⟩ :=
        hhard d n a b hbd u hu v hv huv hsep hstrict2d hhardreg
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
