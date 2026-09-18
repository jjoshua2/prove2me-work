import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.moment_all_endpoint_monotone_routes (d m : ℕ) (hm : d < m) (a : Fin m → ℝ)
    (ha : Function.Injective a) (u v : Fin d → ℝ) :
    let row : (Fin d → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin d, (a i ^ (j.val+1) - (∑ z, a z ^ (j.val+1)) / (m : ℝ)) * x j
    let P : Set (Fin d → ℝ) := {x | ∀ i, row x i ≤ 1}
    let J : Finset (Fin m) := Finset.univ.filter (fun i => row v i = 1)
    let score : (Fin d → ℝ) → ℝ := fun x => ∑ i ∈ J, row x i
    u ∈ P.extremePoints ℝ → v ∈ P.extremePoints ℝ →
      ∃ L : ℕ, L < Nat.choose m d ∧ ∃ p : ℕ → (Fin d → ℝ),
        p 0 = u ∧ p L = v ∧
        (∀ i, i ≤ L → p i ∈ P.extremePoints ℝ) ∧
        ∀ i, i < L → score (p i) < score (p (i+1)) ∧
          IsExposed ℝ P (segment ℝ (p i) (p (i+1))) ∧
          ∀ j, row (p i) j = 1 → row v j = 1 → row (p (i+1)) j = 1 := by sorry
