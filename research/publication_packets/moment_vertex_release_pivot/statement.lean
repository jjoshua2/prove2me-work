import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.moment_vertex_release_pivot (d m : ℕ) (hm : d < m) (a : Fin m → ℝ)
    (ha : Function.Injective a) (u : Fin d → ℝ) :
    let row : (Fin d → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin d,
        (a i ^ (j.val+1) - (∑ z, a z ^ (j.val+1)) / (m : ℝ)) * x j
    let P : Set (Fin d → ℝ) := {x | ∀ i, row x i ≤ 1}
    let I : Finset (Fin m) := Finset.univ.filter (fun i => row u i = 1)
    u ∈ P.extremePoints ℝ → ∀ p ∈ I,
      ∃ (w : Fin d → ℝ) (t : ℝ) (q : Fin m),
        0 < t ∧ q ∉ I ∧
        row w p = -1 ∧ (∀ i ∈ I.erase p, row w i = 0) ∧
        0 < row w q ∧ t = (1-row u q)/row w q ∧
        (∀ i, 0 < row w i → t ≤ (1-row u i)/row w i) ∧
        u+t • w ∈ P.extremePoints ℝ ∧
        (Finset.univ.filter (fun i => row (u+t • w) i = 1)) = insert q (I.erase p) ∧
        u ≠ u+t • w ∧
        IsExposed ℝ P (segment ℝ u (u+t • w)) ∧ IsExtreme ℝ P (segment ℝ u (u+t • w)) ∧
        {z | z ∈ P ∧ ∀ i ∈ I.erase p, row z i = 1} = segment ℝ u (u+t • w) ∧
        (∀ s : ℝ, 0 ≤ s → ((u+s • w ∈ P) ↔ s ≤ t)) := by sorry
