import Mathlib
open Set
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.exposed_core_edge_has_minkowski_bridge
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (m : ℕ) (c : Fin m) (S : Fin m → Finset E) (hS : ∀ i, (S i).Nonempty)
    (u v : E) (hu : u ∈ S c) (hv : v ∈ S c) (huv : u ≠ v)
    (f₀ : E →ₗ[ℝ] ℝ) (h₀ : f₀ v = f₀ u)
    (hbound₀ : ∀ x ∈ S c, f₀ x ≤ f₀ u)
    (hmax₀ : ∀ x ∈ S c, f₀ x = f₀ u → x ∈ segment ℝ u v) :
    let R : Set E := {z | ∃ x : Fin m → E,
      (∀ i, x i ∈ convexHull ℝ (S i : Set E)) ∧ (∑ i, x i) = z}
    ∃ (f : E →ₗ[ℝ] ℝ) (a b : Fin m → E) (η : Fin m → ℝ),
      f (v-u) = 0 ∧ a c = u ∧ b c = v ∧ η c = 1 ∧
      (∀ i, a i ∈ S i ∧ b i ∈ S i ∧ 0 ≤ η i ∧ b i = a i + η i • (v-u) ∧
        (∀ x ∈ S i, f x ≤ f (a i)) ∧
        {x | x ∈ convexHull ℝ (S i : Set E) ∧ f x = f (a i)} =
          segment ℝ (a i) (b i)) ∧
      (∑ i, a i) ≠ (∑ i, b i) ∧
      (∀ z ∈ R, f z ≤ f (∑ i, a i)) ∧
      {z | z ∈ R ∧ f z = f (∑ i, a i)} = segment ℝ (∑ i, a i) (∑ i, b i) ∧
      IsExtreme ℝ R (segment ℝ (∑ i, a i) (∑ i, b i)) := by sorry
