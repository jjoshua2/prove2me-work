import Mathlib
set_option autoImplicit false

theorem Hirsch.parallel_displacements_force_affine_coordinate_levels
    {E I : Type*} [AddCommGroup E] [Module ℝ E] [Fintype I]
    (V : Finset E) (p q : I → E) (g : E) (lambda : I → ℝ)
    (hp : ∀ i, p i ∈ V) (hq : ∀ i, q i ∈ V)
    (hg : g ≠ 0) (hpos : ∀ i, 0 < lambda i)
    (hinj : Function.Injective lambda)
    (hdisp : ∀ i, q i - p i = lambda i • g)
    (r : ℕ) (T : E →ₗ[ℝ] (Fin r → ℝ))
    (hT : Function.Injective T) (offset : Fin r → ℝ) :
    ∃ j : Fin r, (T g) j ≠ 0 ∧
      2 * Fintype.card I ≤
        (V.image (fun x => (T x) j + offset j)).card *
          ((V.image (fun x => (T x) j + offset j)).card - 1) := by sorry
