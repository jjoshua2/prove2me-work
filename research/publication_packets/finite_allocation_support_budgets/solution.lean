import Theorems.Thm_Hirsch_finite_allocation_minkowski_criterion
import Theorems.Thm_Hirsch_primal_dual_support_budget_exact

open Set
open scoped BigOperators

/-- Compose the accepted finite-allocation criterion with exact original-H
primal/dual support witnesses. -/
theorem solution
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
        ∀ (alpha : Finset (Fin m ⊕ Option (Fin k)) → Fin m → ℝ)
          (xstar : Finset (Fin m ⊕ Option (Fin k)) → E),
          (∀ s i, 0 ≤ alpha s i) →
          (∀ s i, a i (xstar s) ≤ b i) →
          (∀ s x : E,
            (∑ i, c s (.inl i) * a i x) = ∑ i, alpha s i * a i x) →
          (∀ s i, alpha s i * (b i - a i (xstar s)) = 0) →
          (({x : E | ∀ i, a i x ≤ b i} =
            {x : E | ∃ p : E, (∀ i, a i p ≤ b i - h i) ∧
              ∃ θ : Fin k → ℝ, (∀ j, 0 ≤ θ j) ∧ (∑ j, θ j) ≤ t ∧ p + G θ = x}) ↔
            ∀ s,
              (∑ i, c s (.inl i) * h i) - c s (.inr none) * t ≤
                (∑ i, c s (.inl i) * b i) - ∑ i, alpha s i * b i) := by
  classical
  obtain ⟨c, hc, halloc⟩ := Hirsch.finite_allocation_minkowski_criterion m k a G
  refine ⟨c, hc, ?_⟩
  intro b h t ht hsupport alpha xstar halpha hxstar hforms hcomp
  rw [halloc b h t ht hsupport]
  constructor
  · intro hall s
    let lambda : Fin m → ℝ := fun i => c s (.inl i)
    let K : ℝ := (∑ i, lambda i * h i) - c s (.inr none) * t
    have huniv : ∀ x : E, (∀ i, a i x ≤ b i) →
        K ≤ (∑ i, lambda i * b i) - ∑ i, lambda i * a i x := by
      intro x hx
      have hs := hall x hx s
      simp only [mul_sub, Finset.sum_sub_distrib] at hs
      dsimp [K, lambda]
      linarith
    have hexact :=
      (Hirsch.primal_dual_support_budget_exact a b lambda (alpha s) (xstar s) K
        (halpha s) (hxstar s) (hforms s) (hcomp s)).mp huniv
    simpa [K, lambda] using hexact
  · intro hscalar x hx s
    let lambda : Fin m → ℝ := fun i => c s (.inl i)
    let K : ℝ := (∑ i, lambda i * h i) - c s (.inr none) * t
    have hexact : K ≤ (∑ i, lambda i * b i) - ∑ i, alpha s i * b i := by
      simpa [K, lambda] using hscalar s
    have huniv :=
      (Hirsch.primal_dual_support_budget_exact a b lambda (alpha s) (xstar s) K
        (halpha s) (hxstar s) (hforms s) (hcomp s)).mpr hexact
    have hxbudget := huniv x hx
    simp only [mul_sub, Finset.sum_sub_distrib]
    dsimp [K, lambda] at hxbudget
    linarith

#print axioms solution
