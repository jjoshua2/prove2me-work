import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.moment_quantitative_neighbor_transport (d m : ℕ) (hm : d < m) (a : Fin m → ℝ)
    (ha : Function.Injective a) (u v : Fin d → ℝ) :
    let row : (Fin d → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin d, (a i ^ (j.val+1) - (∑ z, a z ^ (j.val+1)) / (m : ℝ)) * x j
    let P : Set (Fin d → ℝ) := {x | ∀ i, row x i ≤ 1}
    let I : Finset (Fin m) := Finset.univ.filter (fun i => row u i = 1)
    let J : Finset (Fin m) := Finset.univ.filter (fun i => row v i = 1)
    let score : (Fin d → ℝ) → ℝ := fun x => ∑ i ∈ J, row x i
    u ∈ P.extremePoints ℝ → v ∈ P.extremePoints ℝ → u ≠ v →
      ∃ (w : I → (Fin d → ℝ)) (t : I → ℝ),
        (∀ p : I, 0 < t p ∧
          (∀ i : I, row (w p) i.val = if i = p then -1 else 0) ∧
          u + t p • w p ∈ P.extremePoints ℝ ∧
          IsExposed ℝ P (segment ℝ u (u + t p • w p))) ∧
        let b : I → ℝ := fun p => (1-row v p.val) / t p
        let mass : ℝ := ∑ p : I, b p
        (∀ p, 0 ≤ b p) ∧ 1 ≤ mass ∧
        v-u = ∑ p : I, b p • ((u + t p • w p)-u) ∧
        ∃ p : I, 0 < b p ∧ score u < score (u + t p • w p) ∧
          score v-score u ≤ mass * (score (u + t p • w p)-score u) ∧
          ∀ i : Fin m, row u i = 1 → row v i = 1 →
            row (u + t p • w p) i = 1 := by sorry
