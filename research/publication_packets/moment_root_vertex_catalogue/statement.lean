import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.moment_root_polynomial_vertex_catalogue (d m : ℕ) (hm : d < m) (a : Fin m → ℝ)
    (ha : Function.Injective a) :
    let row : (Fin d → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin d, (a i ^ (j.val+1) - (∑ z, a z ^ (j.val+1)) / (m : ℝ)) * x j
    let q : Finset (Fin m) → Polynomial ℝ :=
      fun S => ∏ i ∈ S, (Polynomial.X - Polynomial.C (a i))
    let μ : Finset (Fin m) → ℝ := fun S => (∑ i : Fin m, (q S).eval (a i)) / (m : ℝ)
    let v : Finset (Fin m) → (Fin d → ℝ) := fun S j => -(q S).coeff (j.val+1) / μ S
    let F : Finset (Finset (Fin m)) :=
      (Finset.powersetCard d Finset.univ).filter
        (fun S => μ S ≠ 0 ∧ ∀ i : Fin m, 0 ≤ (q S).eval (a i) / μ S)
    Set.InjOn v F ∧
      (∀ x : Fin d → ℝ,
        x ∈ ({y | ∀ i, row y i ≤ 1}).extremePoints ℝ ↔ x ∈ F.image v) ∧
      (∀ S ∈ F, ∀ i : Fin m, row (v S) i = 1 ↔ i ∈ S) ∧
      (F.image v).card = F.card ∧ F.card ≤ Nat.choose m d := by sorry
