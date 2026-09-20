import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.zonotope_completion_original_direction_obstruction (d m r : ℕ) (C : Finset (Fin d → ℝ))
    (Q : Set (Fin d → ℝ)) (hQc : IsCompact Q) (hQne : Q.Nonempty)
    (w : Fin m → (Fin d → ℝ)) (a b : Fin r → (Fin d → ℝ)) :
    let P : Set (Fin d → ℝ) := convexHull ℝ (C : Set (Fin d → ℝ))
    let Z : Set (Fin d → ℝ) := {x | ∃ s : Fin m → ℝ,
      (∀ i, 0 ≤ s i ∧ s i ≤ 1) ∧ (∑ i : Fin m, s i • w i)=x}
    {z | ∃ x ∈ P, ∃ y ∈ Q, x+y=z} = Z →
    (∀ i, a i ∈ P ∧ b i ∈ P ∧ a i ≠ b i ∧
      IsExposed ℝ P (segment ℝ (a i) (b i))) →
    (∀ i j : Fin r, ∀ c : ℝ, b i-a i=c • (b j-a j) → i=j) →
    (∃ selected : Fin r → Fin m, Function.Injective selected ∧
      ∀ i, w (selected i) ≠ 0 ∧ ∃ c : ℝ, w (selected i)=c • (b i-a i)) ∧
    r ≤ m ∧ ∃ u v : Fin d → ℝ,
      u ∈ Z.extremePoints ℝ ∧ v ∈ Z.extremePoints ℝ ∧ u+v=∑ i : Fin m, w i ∧
      ∀ L : ℕ, ∀ p : Fin (L+1) → (Fin d → ℝ),
        p 0=u → p (Fin.last L)=v → (∀ i, p i ∈ Z) →
        (∀ i : Fin L, p i.castSucc ≠ p i.succ ∧
          IsExposed ℝ Z (segment ℝ (p i.castSucc) (p i.succ))) → r ≤ L := by sorry
