import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open Set Hirsch

/-!
  Remaining open leaf of the polynomial Hirsch reduction.

  Already-on-the-face is immediate (stationary walk). The genuine content is a
  uniform polynomial budget for walking from `u` onto a prescribed supporting
  hyperplane of `v`. Kalai–Kleitman / Larman / connectedness do not supply that
  budget: they are the wrong growth, or supply some walk with no polynomial
  length. Do not close this file with those theorems.
-/

/-- If `u` already lies on the prescribed supporting hyperplane, take `z = u`
and a stationary walk of any length. -/
lemma already_on_face_access {d n : ℕ} {C k : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {u : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    {i : Fin n} (hiu : ⟪a i, u⟫ = b i) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (C * (n + d) ^ k) = z ∧
        ∀ j < C * (n + d) ^ k,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  refine ⟨u, hu, hiu, fun _ => u, rfl, rfl, ?_⟩
  intro _ _
  exact Or.inl rfl

/-- Off-face routing with a uniform polynomial budget is the remaining
conjecture. `graph_connected_general` gives some walk; Kalai–Kleitman /
Larman give the wrong growth. Do not submit this file until that case is
proved without `sorry`. -/
