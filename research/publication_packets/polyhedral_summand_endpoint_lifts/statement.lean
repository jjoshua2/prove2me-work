import Mathlib
set_option autoImplicit false

theorem Hirsch.polyhedral_summand_endpoint_lifts_and_routes (d m B : ℕ)
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (Q : Set (Fin d → ℝ)) (hQ : Convex ℝ Q) (hQc : IsCompact Q) (hQne : Q.Nonempty) :
    let P : Set (Fin d → ℝ) := {x | ∀ i, A i x ≤ b i}
    let R : Set (Fin d → ℝ) := {z | ∃ x ∈ P, ∃ y ∈ Q, x+y=z}
    (∀ u ∈ P.extremePoints ℝ, ∃ q ∈ Q.extremePoints ℝ, u+q ∈ R.extremePoints ℝ) ∧
    ((∀ z₀ ∈ R.extremePoints ℝ, ∀ z₁ ∈ R.extremePoints ℝ,
      ∃ N : ℕ, N ≤ B ∧ ∃ z : ℕ → (Fin d → ℝ),
        z 0=z₀ ∧ z N=z₁ ∧ (∀ i, i ≤ N → z i ∈ R.extremePoints ℝ) ∧
        ∀ i, i < N → z i ≠ z (i+1) ∧ IsExposed ℝ R (segment ℝ (z i) (z (i+1)))) →
      ∀ u ∈ P.extremePoints ℝ, ∀ v ∈ P.extremePoints ℝ,
      ∃ L : ℕ, L ≤ B ∧ ∃ p : ℕ → (Fin d → ℝ),
        p 0=u ∧ p L=v ∧ (∀ i, i ≤ L → p i ∈ P.extremePoints ℝ) ∧
        ∀ i, i < L → p i ≠ p (i+1) ∧
          IsExposed ℝ P (segment ℝ (p i) (p (i+1))) ∧
          IsExtreme ℝ P (segment ℝ (p i) (p (i+1)))) := by sorry
