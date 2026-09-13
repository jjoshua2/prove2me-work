import Mathlib
open Set
open scoped BigOperators

theorem Hirsch.segment_summand_equality_of_finite_farkas_weights
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι]
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g : E) (τ : ℝ)
    (hτ : 0 ≤ τ) (hplus : ∃ i, 0 < a i g)
    (cert : ∀ i j, 0 < a i g → a j g < 0 →
      ∃ w : ι → ℝ,
        (∀ k, 0 ≤ w k) ∧
        (∑ k, w k • a k) = (-a j g) • a i + (a i g) • a j ∧
        (∑ k, w k * b k) ≤
          (-a j g) * b i + (a i g) * b j - τ * (a i g) * (-a j g)) :
    {x : E | ∀ i, a i x ≤ b i} =
      {x : E | ∃ p : E,
        (∀ i, a i p ≤ b i - τ * max (a i g) 0) ∧
        ∃ t : ℝ, 0 ≤ t ∧ t ≤ τ ∧ x = p + t • g} := by sorry
