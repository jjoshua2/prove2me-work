import Mathlib
open Set
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.generic_fibre_objectives_without_independent_ties
    {E A B I : Type*} [AddCommGroup E] [Module ℝ E]
    [Fintype A] [Fintype B] [Fintype I]
    (f₀ g₀ : E →ₗ[ℝ] ℝ) (c₀ : A → E) (c₁ : B → E) (v : I → E)
    (hc₀ : ∀ a, f₀ (c₀ a) < 0)
    (hc₁ : ∀ b, g₀ (c₁ b) < 0)
    (hv : ∀ i, v i ≠ 0) :
    ∃ f g : E →ₗ[ℝ] ℝ,
      (∀ a, f (c₀ a) < 0) ∧
      (∀ b, g (c₁ b) < 0) ∧
      (∀ i, f (v i) ≠ 0) ∧
      (∀ i, g (v i) ≠ 0) ∧
      (∀ i j, v j ∉ Submodule.span ℝ ({v i} : Set E) →
        f (v i)*g (v j)-f (v j)*g (v i) ≠ 0) ∧
      ∀ (t : ℝ) (i j : I),
        ((1-t)*f (v i)+t*g (v i)=0) →
        ((1-t)*f (v j)+t*g (v j)=0) →
        v j ∈ Submodule.span ℝ ({v i} : Set E) := by sorry
