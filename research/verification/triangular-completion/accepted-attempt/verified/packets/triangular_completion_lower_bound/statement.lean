import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.triangular_all_zonotope_completions_exponential (e : ℝ) (he : 0 < e) (he2 : e < 1/2) (n m : ℕ)
    (Q : Set (Fin (n+1) → ℝ)) (hQc : IsCompact Q) (hQne : Q.Nonempty)
    (w : Fin m → (Fin (n+1) → ℝ)) :
    let P : Set (Fin (n+1) → ℝ) := {x |
      (0 ≤ x (Fin.last n) ∧ x (Fin.last n) ≤ 1) ∧
      ∀ i : Fin n, e*x i.succ ≤ x i.castSucc ∧ x i.castSucc ≤ 1-e*x i.succ}
    let Z : Set (Fin (n+1) → ℝ) := {x | ∃ s : Fin m → ℝ,
      (∀ i, 0 ≤ s i ∧ s i ≤ 1) ∧ (∑ i : Fin m, s i • w i)=x}
    {z | ∃ x ∈ P, ∃ y ∈ Q, x+y=z}=Z →
    2^n ≤ m ∧ ∃ u v : Fin (n+1) → ℝ,
      u ∈ Z.extremePoints ℝ ∧ v ∈ Z.extremePoints ℝ ∧ u+v=∑ i : Fin m, w i ∧
      ∀ L : ℕ, ∀ p : Fin (L+1) → (Fin (n+1) → ℝ),
        p 0=u → p (Fin.last L)=v → (∀ i, p i ∈ Z) →
        (∀ i : Fin L, p i.castSucc ≠ p i.succ ∧
          IsExposed ℝ Z (segment ℝ (p i.castSucc) (p i.succ))) → 2^n ≤ L := by sorry
