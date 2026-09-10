import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch

/-- Local workspace stub for the public Prove2Me theorem
`Hirsch.target_face_access_of_local_neutral_rank`
(ID 4da3a606-c8d4-4570-a246-afbff569cc7a). Platform verification must
resolve this import to the public Proved theorem. -/
theorem target_face_access_of_local_neutral_rank
    (d n r : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (huv : u ≠ v)
    (hlocal : ∀ x ∈ extremePoints ℝ (Hpoly a b),
      (∀ i, a i ≠ 0 → ⟪a i, v⟫ = b i → ⟪a i, x⟫ ≠ b i) →
      ∃ K : Submodule ℝ (EuclideanSpace ℝ (Fin d)),
        Module.finrank ℝ K ≤ r ∧
        ∀ i, a i ≠ 0 → ⟪a i, u⟫ ≠ b i → ⟪a i, v⟫ ≠ b i →
          ⟪a i, x⟫ = b i → a i ∈ K) :
    ∃ (i : Fin n) (z : EuclideanSpace ℝ (Fin d)),
      a i ≠ 0 ∧ ⟪a i, v⟫ = b i ∧
      z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (n * 2 ^ (r - 3) + 1) = z ∧
        ∀ j < n * 2 ^ (r - 3) + 1,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by sorry

end Hirsch
