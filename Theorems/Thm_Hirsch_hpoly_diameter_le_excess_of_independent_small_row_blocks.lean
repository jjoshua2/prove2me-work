import Mathlib
import Definitions.Def_Hirsch_model
open scoped BigOperators RealInnerProductSpace
open Set Hirsch

namespace Hirsch
theorem hpoly_diameter_le_excess_of_independent_small_row_blocks
    {d n k : ℕ} (dims counts : Fin k → ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ]
      (∀ i : Fin k, EuclideanSpace ℝ (Fin (dims i))))
    (e : (Σ i : Fin k, Fin (counts i)) ≃ Fin n)
    (A : ∀ i : Fin k, Fin (counts i) → EuclideanSpace ℝ (Fin (dims i)))
    (hrows : ∀ z i j, ⟪a (e ⟨i, j⟩), T.symm z⟫ = ⟪A i j, z i⟫)
    (hbd : Bornology.IsBounded (Hpoly a b)) (hne : (Hpoly a b).Nonempty)
    (hcount : ∀ i, dims i ≤ counts i)
    (hsmallcount : ∀ i, counts i ≤ dims i + 3) :
    DiamLE (Hpoly a b) (n - d) := by sorry
end Hirsch
