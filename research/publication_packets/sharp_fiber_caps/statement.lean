import Mathlib
open Set

theorem Hirsch.sharp_fiber_caps_every_segment_summand
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι]
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g x : E) (τ s : ℝ)
    (i j : ι) (hi : 0 < a i g) (hj : a j g < 0)
    (hx : ∀ k, a k x ≤ b k)
    (hsharp : (-a j g)*(b i-a i x)+(a i g)*(b j-a j x) =
      τ*(a i g)*(-a j g))
    (P : Set E) (hs : 0 ≤ s)
    (hdecomp : {y : E | ∀ k, a k y ≤ b k} =
      {y : E | ∃ p ∈ P, ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ y = p+t • g}) : s ≤ τ := by sorry
