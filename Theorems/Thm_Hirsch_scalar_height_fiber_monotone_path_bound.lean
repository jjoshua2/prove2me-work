import Definitions.Def_Hirsch_scalar_fiber_model

set_option autoImplicit false
open scoped RealInnerProductSpace BigOperators

/-- Mathematical result from the PR #11 scalar-fiber analysis; this declaration
is a formalization target, not yet a Lean proof.  Strictly decreasing factor
paths synchronize, so independent scalar-height gluing cannot multiply their
lengths. -/
theorem Hirsch.scalar_height_fiber_monotone_path_bound :
    ∀ (k d : ℕ)
      (P : Fin k → Set (EuclideanSpace ℝ (Fin d)))
      (h : Fin k → EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] ℝ)
      (L : Fin k → ℕ)
      (u v : Fin k → EuclideanSpace ℝ (Fin d)),
      (∀ i, Convex ℝ (P i)) →
      (∀ i, Hirsch.StrictHeightEdgeWalk (P i) (h i) (L i) (u i) (v i)) →
      (∀ i j, h i (u i) = h j (u j)) →
      (∀ i j, h i (v i) = h j (v j)) →
      Hirsch.EndpointWalkLE (Hirsch.ScalarHeightFiber P h)
        (1 + ∑ i, (L i - 1)) u v := by sorry
