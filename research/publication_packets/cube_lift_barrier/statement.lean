import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.cube_fibre_lift_exponential_barrier (d m : ℕ) (w : Fin m → (Fin d → ℝ))
    (label : Finset (Fin d) → Fin m)
    (hlabel : ∀ S : Finset (Fin d), S.Nonempty → ∀ j,
      w (label S) j = if j ∈ S then 1 else 0)
    (Q : Set (Fin d → ℝ)) (q₀ q₁ : Fin d → ℝ) (hq₀ : q₀ ∈ Q) (hq₁ : q₁ ∈ Q) :
    let Z : Set (Fin d → ℝ) := {z | ∃ s : Fin m → ℝ,
      (∀ i, 0 ≤ s i ∧ s i ≤ 1) ∧ (∑ i : Fin m, s i • w i)=z}
    (∀ x : Fin d → ℝ, (∀ j, 0 ≤ x j ∧ x j ≤ 1) → ∀ q ∈ Q, x+q ∈ Z) →
    q₀ ∈ Z.extremePoints ℝ → (fun _ : Fin d => (1 : ℝ))+q₁ ∈ Z.extremePoints ℝ →
    ∀ L : ℕ, ∀ p : Fin (L+1) → (Fin d → ℝ),
      p 0=q₀ → p (Fin.last L)=(fun _ => (1 : ℝ))+q₁ → (∀ i, p i ∈ Z) →
      (∀ i : Fin L, p i.castSucc ≠ p i.succ ∧
        IsExposed ℝ Z (segment ℝ (p i.castSucc) (p i.succ))) → 2^d ≤ L+1 := by sorry
