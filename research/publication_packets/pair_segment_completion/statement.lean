import Mathlib
open scoped BigOperators Pointwise
set_option autoImplicit false

theorem Hirsch.finite_hull_pair_segment_completion (d n : ℕ) (hn : 0 < n) (v : Fin n → (Fin d → ℝ)) :
    let Z : Set (Fin d → ℝ) :=
      {z | ∃ t : (Fin n × Fin n) → ℝ,
        (∀ e, 0 ≤ t e ∧ t e ≤ 1) ∧
        (∑ e : Fin n × Fin n, (t e • v e.1+(1-t e) • v e.2))=z}
    let Q : Set (Fin d → ℝ) := {q | ∀ i, q+v i ∈ Z}
    IsCompact Z ∧ Convex ℝ Z ∧ IsCompact Q ∧ Convex ℝ Q ∧ Q.Nonempty ∧
      Z = {z | ∃ p ∈ convexHull ℝ (Set.range v), ∃ q ∈ Q, p+q=z} ∧
      Fintype.card (Fin n × Fin n) = n^2 := by sorry
