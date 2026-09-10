import Mathlib
import Definitions.Def_Hirsch_model
import Solutions.PolynomialLogLocalRankReduction
import Solutions.PolynomialProductWalk

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschLogRank

/-- It suffices to solve polynomial target-face access only on instances that
actually exhibit a target-avoiding vertex whose canonical active-neutral span
has rank greater than `log_2(n+d)+3`.

All complementary instances already have a quadratic target-face route by
`target_access_or_large_local_neutral_rank`. Thus this hypothesis is a strict
structural restriction of the open routing problem, not merely a renaming of
polynomial target access. -/
theorem full_target_access_of_large_local_neutral_rank_regime
    (hhard : ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hpoly a b) →
      ∀ u ∈ extremePoints ℝ (Hpoly a b),
      ∀ v ∈ extremePoints ℝ (Hpoly a b), u ≠ v →
      (∀ j, a j ≠ 0 → ⟪a j, u⟫ ≠ b j ∨ ⟪a j, v⟫ ≠ b j) →
      (∃ x : EuclideanSpace ℝ (Fin d),
        x ∈ extremePoints ℝ (Hpoly a b) ∧
        (∀ i, a i ≠ 0 → ⟪a i, v⟫ = b i → ⟪a i, x⟫ ≠ b i) ∧
        Nat.log 2 (n + d) + 3 <
          Module.finrank ℝ (activeNeutralSpan a b u v x)) →
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
  let N : ℕ := n + d
  have hdpos : 0 < d := by
    by_contra hd
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    subst d
    exact huv (Subsingleton.elim _ _)
  have hN : 1 ≤ N := by
    dsimp [N]
    omega
  have hpow2 : N ^ 2 ≤ N ^ k' := by
    dsimp [k']
    rw [pow_add]
    have hk : 1 ≤ N ^ k := one_le_pow₀ hN
    have hmul := Nat.mul_le_mul_right (N ^ 2) hk
    simpa [Nat.mul_comm] using hmul
  have hpowk : N ^ k ≤ N ^ k' := by
    dsimp [k']
    rw [pow_add]
    have h2 : 1 ≤ N ^ 2 := one_le_pow₀ hN
    simpa using Nat.mul_le_mul_left (N ^ k) h2
  have hC : C ≤ C' := by
    dsimp [C']
    omega
  have hC2 : 2 ≤ C' := by
    dsimp [C']
    omega
  rcases target_access_or_large_local_neutral_rank d n a b hbd u v hu hv huv with
    heasy | hlarge
  · obtain ⟨i, z, hai, hiv, hz, hiz, w, hw0, hwB, hwstep⟩ := heasy
    have hbudget : 2 * N ^ 2 ≤ C' * N ^ k' := Nat.mul_le_mul hC2 hpow2
    obtain ⟨w', hw'0, hw'D, hw'step⟩ :=
      HirschProduct.pad_walk (Adj (Hpoly a b)) hbudget w
        (by simpa [N] using hw0) (by simpa [N] using hwB)
        (by simpa [N] using hwstep)
    refine ⟨i, z, hai, hiv, hz, hiz, w', hw'0, ?_, ?_⟩
    · simpa [N, C', k'] using hw'D
    · simpa [N, C', k'] using hw'step
  · obtain ⟨i, z, hai, hiv, hz, hiz, w, hw0, hwB, hwstep⟩ :=
      hhard d n a b hbd u hu v hv huv hsep hlarge
    have hbudget : C * N ^ k ≤ C' * N ^ k' := Nat.mul_le_mul hC hpowk
    obtain ⟨w', hw'0, hw'D, hw'step⟩ :=
      HirschProduct.pad_walk (Adj (Hpoly a b)) hbudget w
        (by simpa [N] using hw0) (by simpa [N] using hwB)
        (by simpa [N] using hwstep)
    refine ⟨i, z, hai, hiv, hz, hiz, w', hw'0, ?_, ?_⟩
    · simpa [N, C', k'] using hw'D
    · simpa [N, C', k'] using hw'step

#print axioms full_target_access_of_large_local_neutral_rank_regime

end HirschLogRank
