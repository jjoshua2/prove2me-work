import Mathlib
import Definitions.Def_Hirsch_model
import Theorems.Thm_Hirsch_diameter_bound_of_target_face_access
import Solutions.PolynomialProductWalk

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace Hirsch

/-- The existential target-face-access statement is already enough for the
full Polynomial Hirsch conjecture; the balanced-family intermediate theorem is
not logically needed.  One target-access block per dimension gives
`d * C * (n+d)^k`, and `d ≤ n+d` absorbs that extra factor into exponent
`k+1`. -/
theorem polynomial_hirsch_of_target_face_access
    (haccess : ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hpoly a b) →
      ∀ u ∈ extremePoints ℝ (Hpoly a b),
      ∀ v ∈ extremePoints ℝ (Hpoly a b), u ≠ v →
      (∀ i, a i ≠ 0 → ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i) →
      ∃ (i : Fin n) (z : EuclideanSpace ℝ (Fin d)),
        a i ≠ 0 ∧ ⟪a i, v⟫ = b i ∧
        z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
        ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
          w 0 = u ∧ w (C * (n + d) ^ k) = z ∧
          ∀ j < C * (n + d) ^ k,
            w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1))) :
    ∃ c k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      (Hpoly a b).Nonempty → Bornology.IsBounded (Hpoly a b) →
      DiamLE (Hpoly a b) (c * (n + d) ^ k) := by
  obtain ⟨C, k, haccess⟩ := haccess
  refine ⟨C, k + 1, ?_⟩
  intro d n a b _hne hbd
  have hD : DiamLE (Hpoly a b) (d * C * (n + d) ^ k) :=
    diameter_bound_of_target_face_access C k haccess d n a b hbd
  have hdN : d ≤ n + d := by omega
  have hbudget : d * C * (n + d) ^ k ≤ C * (n + d) ^ (k + 1) := by
    calc
      d * C * (n + d) ^ k = d * (C * (n + d) ^ k) := by ring
      _ ≤ (n + d) * (C * (n + d) ^ k) :=
        Nat.mul_le_mul_right (C * (n + d) ^ k) hdN
      _ = C * (n + d) ^ (k + 1) := by
        rw [pow_succ]
        ring
  intro u hu v hv
  obtain ⟨w, hw0, hwB, hwstep⟩ := hD u hu v hv
  exact HirschProduct.pad_walk (Adj (Hpoly a b)) hbudget
    w hw0 hwB hwstep

#print axioms polynomial_hirsch_of_target_face_access

end Hirsch
