import Mathlib
import Definitions.Def_Hirsch_model
import Theorems.Thm_Hirsch_larman_bound
import Solutions.PolynomialLocalRankAccessCore

open scoped RealInnerProductSpace
open Set Hirsch HirschPolynomialAccess

set_option maxHeartbeats 5000000

noncomputable section

/-- Local neutral rank controls access to some target supporting face.
Unlike a global rank hypothesis, the rank-r subspace may vary with x and need
contain only the neutral normals active at x. This is not prescribed-face
access, a walk to v, or an unconditional polynomial diameter theorem. -/
theorem solution
    (d n r : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (huv : u ≠ v)
    (hlocal : ∀ x ∈ extremePoints ℝ (Hpoly a b),
      (∀ i, a i ≠ 0 → ⟪a i, v⟫ = b i → ⟪a i, x⟫ ≠ b i) →
      ∃ K : Submodule ℝ (EuclideanSpace ℝ (Fin d)),
        Module.finrank ℝ K ≤ r ∧
        ∀ i, a i ≠ 0 → ⟪a i, u⟫ ≠ b i → ⟪a i, v⟫ ≠ b i →
          ⟪a i, x⟫ = b i → a i ∈ K) :
    ∃ (i : Fin n) (z : EuclideanSpace ℝ (Fin d)),
      a i ≠ 0 ∧ ⟪a i, v⟫ = b i ∧
      z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (n * 2 ^ (r - 3) + 1) = z ∧
        ∀ j < n * 2 ^ (r - 3) + 1,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  have hconnect : ∃ D : ℕ, ∃ wg : ℕ → EuclideanSpace ℝ (Fin d),
      wg 0 = u ∧ wg D = v ∧
      ∀ j < D, wg j = wg (j + 1) ∨ Adj (Hpoly a b) (wg j) (wg (j + 1)) := by
    obtain ⟨w, hw0, hwD, hwstep⟩ :=
      Hirsch.larman_bound d n a b ⟨u, hu.1⟩ hbd u hu v hv
    exact ⟨n * 2 ^ (d - 3), w, hw0, hwD, hwstep⟩
  have hlow : ∀ (e : ℕ), e ≤ r →
      ∀ (a' : Fin n → EuclideanSpace ℝ (Fin e)) (b' : Fin n → ℝ),
        (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
        DiamLE (Hpoly a' b') (n * 2 ^ (r - 3)) := by
    intro e her a' b' hne hbd' p hp q hq
    obtain ⟨w, hw0, hwB, hwstep⟩ :=
      Hirsch.larman_bound e n a' b' hne hbd' p hp q hq
    let A : ℕ := n * 2 ^ (e - 3)
    let B : ℕ := n * 2 ^ (r - 3)
    have hAB : A ≤ B := Nat.mul_le_mul_left n
      (Nat.pow_le_pow_right (by omega) (Nat.sub_le_sub_right her 3))
    let wp : ℕ → EuclideanSpace ℝ (Fin e) := fun j => w (min j A)
    refine ⟨wp, ?_, ?_, ?_⟩
    · change w (min 0 A) = p
      rw [Nat.zero_min]
      exact hw0
    · change w (min B A) = q
      rw [Nat.min_eq_right hAB]
      exact hwB
    · intro j hj
      by_cases hjA : j < A
      · have hj0 : j ≤ A := by omega
        have hj1 : j + 1 ≤ A := by omega
        simpa only [wp, Nat.min_eq_left hj0, Nat.min_eq_left hj1] using hwstep j hjA
      · have hAj : A ≤ j := by omega
        have hAj1 : A ≤ j + 1 := by omega
        exact Or.inl (by simp only [wp, Nat.min_eq_right hAj, Nat.min_eq_right hAj1])
  exact target_face_access_of_local_neutral_rank_core d n r (n * 2 ^ (r - 3))
    a b hbd u v hu hv huv hlocal hconnect hlow

#print axioms solution
