import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.moment_six_row_no_uniform_local_contraction (δ : ℝ) (hδ : 0 < δ) :
    ∃ e : ℝ, 0 < e ∧ e < 1/4 ∧
      let a : Fin 6 → ℝ := ![-1,0,e,2*e,3*e,1]
      let u : Fin 2 → ℝ := ![9*e/(1+4*e^2),-3/(1+4*e^2)]
      let l : Fin 2 → ℝ := ![3*e/(1+4*e^2),-3/(1+4*e^2)]
      let r : Fin 2 → ℝ := ![15*e/(1+10*e^2),-3/(1+10*e^2)]
      let v : Fin 2 → ℝ := ![0,3/(2-7*e^2)]
      let A : (Fin 2 → ℝ) → Fin 6 → ℝ := fun x i =>
        ∑ j : Fin 2, (a i ^ (j.val+1) - (∑ k, a k ^ (j.val+1))/(6 : ℝ))*x j
      let P : Set (Fin 2 → ℝ) := {x | ∀ i, A x i ≤ 1}
      let f : (Fin 2 → ℝ) → ℝ := fun x => A x 0 + A x 5
      u ∈ P.extremePoints ℝ ∧ v ∈ P.extremePoints ℝ ∧ u ≠ v ∧
      0 < f v-f u ∧ l ≠ r ∧
      (∀ z : Fin 2 → ℝ,
        (z ∈ P.extremePoints ℝ ∧ z ≠ u ∧ IsExposed ℝ P (segment ℝ u z)) ↔ z=l ∨ z=r) ∧
      (∀ z : Fin 2 → ℝ,
        (z ∈ P.extremePoints ℝ ∧ z ≠ u ∧ IsExposed ℝ P (segment ℝ u z)) →
          0 < f z-f u ∧ f z-f u < δ*(f v-f u)) ∧
      ∃ path : Fin 4 → (Fin 2 → ℝ), path 0=u ∧ path 3=v ∧
        (∀ i, path i ∈ P.extremePoints ℝ) ∧
        ∀ i : Fin 3, path i.castSucc ≠ path i.succ ∧
          IsExposed ℝ P (segment ℝ (path i.castSucc) (path i.succ)) := by sorry
