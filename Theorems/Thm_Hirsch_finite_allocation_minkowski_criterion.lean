import Mathlib
open Set
open scoped BigOperators

namespace Hirsch

theorem finite_allocation_minkowski_criterion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m k : ℕ) (a : Fin m → E →L[ℝ] ℝ)
    (G : (Fin k → ℝ) →L[ℝ] E) :
    ∃ c : Finset (Fin m ⊕ Option (Fin k)) → ((Fin m ⊕ Option (Fin k)) → ℝ),
      (∀ s, (∀ i, 0 ≤ c s i) ∧
        ∀ j, -(∑ i, c s (.inl i) * a i (G (Pi.single j (1 : ℝ)))) -
          c s (.inr (some j)) + c s (.inr none) = 0) ∧
      ∀ (b h : Fin m → ℝ) (t : ℝ), 0 ≤ t →
        (∀ θ : Fin k → ℝ, (∀ j, 0 ≤ θ j) → (∑ j, θ j) ≤ t →
          ∀ i, a i (G θ) ≤ h i) →
        (({x : E | ∀ i, a i x ≤ b i} =
          {x : E | ∃ p : E, (∀ i, a i p ≤ b i - h i) ∧
            ∃ θ : Fin k → ℝ, (∀ j, 0 ≤ θ j) ∧ (∑ j, θ j) ≤ t ∧ p + G θ = x}) ↔
        (∀ x : E, (∀ i, a i x ≤ b i) → ∀ s,
          0 ≤ (∑ i, c s (.inl i) * (b i - a i x - h i)) + c s (.inr none)*t)) := by
  sorry

end Hirsch
