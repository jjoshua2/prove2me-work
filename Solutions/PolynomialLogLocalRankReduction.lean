import Mathlib
import Definitions.Def_Hirsch_model
import Theorems.Thm_Hirsch_target_face_access_of_local_neutral_rank
import Solutions.PolynomialProductWalk

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschLogRank

variable {d n : ℕ}

/-- Span of the nonzero row normals that are active at `x` but active at
neither endpoint. This is the smallest canonical local subspace that can be
fed to the published local-neutral-rank access theorem. -/
def activeNeutralSpan
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  Submodule.span ℝ (a '' {i : Fin n |
    a i ≠ 0 ∧ ⟪a i, u⟫ ≠ b i ∧ ⟪a i, v⟫ ≠ b i ∧ ⟪a i, x⟫ = b i})

lemma activeNeutral_mem
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d)) (i : Fin n)
    (hai : a i ≠ 0) (hiu : ⟪a i, u⟫ ≠ b i)
    (hiv : ⟪a i, v⟫ ≠ b i) (hix : ⟪a i, x⟫ = b i) :
    a i ∈ activeNeutralSpan a b u v x := by
  apply Submodule.subset_span
  exact ⟨i, ⟨hai, hiu, hiv, hix⟩, rfl⟩

/-- Every bounded H-polytope instance has a sharp local-rank dichotomy.
Either some supporting face of the target is reachable in a quadratic padded
edge budget, or a target-avoiding vertex has active-neutral span rank strictly
larger than `log_2(n+d)+3`.

This is a genuine restriction of the remaining obstruction: the second branch
produces a concrete vertex and a canonical span, rather than merely restating
polynomial target access. No endpoint-separation hypothesis is needed. -/
theorem target_access_or_large_local_neutral_rank
    (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (huv : u ≠ v) :
    (∃ (i : Fin n) (z : EuclideanSpace ℝ (Fin d)),
      a i ≠ 0 ∧ ⟪a i, v⟫ = b i ∧
      z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (2 * (n + d) ^ 2) = z ∧
        ∀ j < 2 * (n + d) ^ 2,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1))) ∨
    (∃ x : EuclideanSpace ℝ (Fin d),
      x ∈ extremePoints ℝ (Hpoly a b) ∧
      (∀ i, a i ≠ 0 → ⟪a i, v⟫ = b i → ⟪a i, x⟫ ≠ b i) ∧
      Nat.log 2 (n + d) + 3 <
        Module.finrank ℝ (activeNeutralSpan a b u v x)) := by
  classical
  let N : ℕ := n + d
  let r : ℕ := Nat.log 2 N + 3
  by_cases hlarge : ∃ x : EuclideanSpace ℝ (Fin d),
      x ∈ extremePoints ℝ (Hpoly a b) ∧
      (∀ i, a i ≠ 0 → ⟪a i, v⟫ = b i → ⟪a i, x⟫ ≠ b i) ∧
      r < Module.finrank ℝ (activeNeutralSpan a b u v x)
  · right
    simpa [r, N] using hlarge
  · left
    have hlocalRank : ∀ x ∈ extremePoints ℝ (Hpoly a b),
        (∀ i, a i ≠ 0 → ⟪a i, v⟫ = b i → ⟪a i, x⟫ ≠ b i) →
        Module.finrank ℝ (activeNeutralSpan a b u v x) ≤ r := by
      intro x hx havoid
      by_contra hnot
      apply hlarge
      exact ⟨x, hx, havoid, Nat.lt_of_not_ge hnot⟩
    have hlocal : ∀ x ∈ extremePoints ℝ (Hpoly a b),
        (∀ i, a i ≠ 0 → ⟪a i, v⟫ = b i → ⟪a i, x⟫ ≠ b i) →
        ∃ K : Submodule ℝ (EuclideanSpace ℝ (Fin d)),
          Module.finrank ℝ K ≤ r ∧
          ∀ i, a i ≠ 0 → ⟪a i, u⟫ ≠ b i → ⟪a i, v⟫ ≠ b i →
            ⟪a i, x⟫ = b i → a i ∈ K := by
      intro x hx havoid
      refine ⟨activeNeutralSpan a b u v x, hlocalRank x hx havoid, ?_⟩
      intro i hai hiu hiv hix
      exact activeNeutral_mem a b u v x i hai hiu hiv hix
    obtain ⟨i, z, hai, hiv, hz, hiz, w, hw0, hwB, hwstep⟩ :=
      Hirsch.target_face_access_of_local_neutral_rank
        d n r a b hbd u v hu hv huv hlocal
    have hdpos : 0 < d := by
      by_contra hd
      have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
      subst d
      exact huv (Subsingleton.elim _ _)
    have hNpos : 0 < N := by
      dsimp [N]
      omega
    have hN0 : N ≠ 0 := Nat.ne_of_gt hNpos
    have hrsub : r - 3 = Nat.log 2 N := by
      dsimp [r]
      omega
    have hpow : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hN0
    have hnN : n ≤ N := by
      dsimp [N]
      omega
    have hmul : n * 2 ^ Nat.log 2 N ≤ n * N := Nat.mul_le_mul_left n hpow
    have hnprod : n * N ≤ N * N := Nat.mul_le_mul_right N hnN
    have hNN : 1 ≤ N * N := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hN0 hN0)
    have hbudget : n * 2 ^ (r - 3) + 1 ≤ 2 * N ^ 2 := by
      rw [hrsub]
      calc
        n * 2 ^ Nat.log 2 N + 1 ≤ n * N + 1 := Nat.add_le_add_right hmul 1
        _ ≤ N * N + 1 := Nat.add_le_add_right hnprod 1
        _ ≤ N * N + N * N := Nat.add_le_add_left hNN (N * N)
        _ = 2 * N ^ 2 := by ring
    obtain ⟨w', hw'0, hw'D, hw'step⟩ :=
      HirschProduct.pad_walk (Adj (Hpoly a b)) hbudget w hw0 hwB hwstep
    refine ⟨i, z, hai, hiv, hz, hiz, w', hw'0, ?_, ?_⟩
    · simpa [N] using hw'D
    · simpa [N] using hw'step

#print axioms activeNeutral_mem
#print axioms target_access_or_large_local_neutral_rank

end HirschLogRank
