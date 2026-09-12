import Mathlib
import Definitions.Def_Hirsch_model
open scoped BigOperators RealInnerProductSpace
open Set Hirsch
namespace Hirsch
theorem hpoly_diameter_le_excess_of_projectively_hidden_small_row_blocks
{d n k : ℕ} (dims counts : Fin k → ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ]
      (∀ i : Fin k, EuclideanSpace ℝ (Fin (dims i))))
    (e : (Σ i : Fin k, Fin (counts i)) ≃ Fin n)
    (A : ∀ i : Fin k, Fin (counts i) → EuclideanSpace ℝ (Fin (dims i)))
    (hrows : ∀ z i j, ⟪a (e ⟨i, j⟩), T.symm z⟫ = ⟪A i j, z i⟫)
    (hbd : Bornology.IsBounded (Hpoly a b)) (hne : (Hpoly a b).Nonempty)
    (hcount : ∀ i, dims i ≤ counts i)
    (hsmallcount : ∀ i, counts i ≤ dims i + 3)
    (c : EuclideanSpace ℝ (Fin d)) (weights inverseWeights : Fin n → ℝ)
    (hweights : ∀ i, 0 ≤ weights i)
    (hnormal : (∑ i, weights i • a i) = -c)
    (hmargin : (∑ i, weights i * b i) < 1)
    (hinverseWeights : ∀ i, 0 ≤ inverseWeights i)
    (hinverseNormal : (∑ i, inverseWeights i • (a i + b i • c)) = c)
    (hinverseMargin : (∑ i, inverseWeights i * b i) < 1) :
    DiamLE (Hpoly (fun i => a i + b i • c) b) (n - d) := by sorry
end Hirsch