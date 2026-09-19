import Mathlib
set_option autoImplicit false

theorem Hirsch.minkowski_summand_exposed_route_contraction (d N : ℕ) (P Q : Set (Fin d → ℝ))
    (hP : Convex ℝ P) (hQ : Convex ℝ Q) (z : ℕ → (Fin d → ℝ))
    (hz : ∀ i, i ≤ N → z i ∈
      ({w | ∃ x ∈ P, ∃ y ∈ Q, x+y=w}).extremePoints ℝ)
    (he : ∀ i, i < N → z i ≠ z (i+1) ∧
      IsExposed ℝ {w | ∃ x ∈ P, ∃ y ∈ Q, x+y=w} (segment ℝ (z i) (z (i+1)))) :
    ∃ a b : ℕ → (Fin d → ℝ),
      (∀ i, i ≤ N → a i ∈ P.extremePoints ℝ ∧ b i ∈ Q.extremePoints ℝ ∧
        a i+b i=z i ∧ ∀ x ∈ P, ∀ y ∈ Q, x+y=z i → x=a i ∧ y=b i) ∧
      (∀ i, i < N →
        IsExposed ℝ P (segment ℝ (a i) (a (i+1))) ∧
        IsExposed ℝ Q (segment ℝ (b i) (b (i+1))) ∧
        ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧
          a (i+1)-a i = α • (z (i+1)-z i) ∧
          b (i+1)-b i = (1-α) • (z (i+1)-z i)) ∧
      (∃ L : ℕ, L ≤ N ∧ ∃ p : ℕ → (Fin d → ℝ),
        p 0=a 0 ∧ p L=a N ∧ (∀ i, i ≤ L → p i ∈ P.extremePoints ℝ) ∧
        ∀ i, i < L → p i ≠ p (i+1) ∧
          IsExposed ℝ P (segment ℝ (p i) (p (i+1))) ∧
          IsExtreme ℝ P (segment ℝ (p i) (p (i+1)))) ∧
      (∃ L : ℕ, L ≤ N ∧ ∃ p : ℕ → (Fin d → ℝ),
        p 0=b 0 ∧ p L=b N ∧ (∀ i, i ≤ L → p i ∈ Q.extremePoints ℝ) ∧
        ∀ i, i < L → p i ≠ p (i+1) ∧
          IsExposed ℝ Q (segment ℝ (p i) (p (i+1))) ∧
          IsExtreme ℝ Q (segment ℝ (p i) (p (i+1)))) := by sorry
