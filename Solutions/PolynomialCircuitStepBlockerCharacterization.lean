import Mathlib
import Solutions.PolynomialCircuitStepCommutation
import Solutions.PolynomialCircuitStepProgress

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschCircuit

variable {d n : ℕ}

/-- For feasible endpoints with circuit displacement, maximality is equivalent
    to the existence of one destination-tight row increasing along the step. -/
theorem rowCircuitStep_iff_target_tight_increasing_row
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ Hpoly a b) (hy : y ∈ Hpoly a b)
    (hg : IsRowCircuit a (y - x)) :
    RowCircuitStep a b x y ↔
      ∃ i : Fin n, a i ≠ 0 ∧ ⟪a i, y⟫ = b i ∧ 0 < ⟪a i, y - x⟫ := by
  constructor
  · intro hstep
    exact HirschCircuitLocalization.rowCircuitStep_exists_target_blocking_row
      a b x y hstep
  · rintro ⟨i, _hai, htight, hpos⟩
    exact rowCircuitStep_of_feasible_of_tight_increasing_row
      a b x y hx hy hg i htight hpos

/-- Exact finite certificate for swapping two already-maximal circuit steps.
    The row supports may overlap. The swapped path preserves both original
    displacement vectors and is maximal exactly when the new intermediate point
    is feasible and each swapped segment has a tight increasing blocker. -/
theorem rowCircuitStep_swap_iff_feasible_and_tight_blockers
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y z : EuclideanSpace ℝ (Fin d))
    (hxy : RowCircuitStep a b x y) (hyz : RowCircuitStep a b y z) :
    let w := x + (z - y)
    (RowCircuitStep a b x w ∧ RowCircuitStep a b w z) ↔
      w ∈ Hpoly a b ∧
      (∃ i : Fin n, a i ≠ 0 ∧ ⟪a i, w⟫ = b i ∧ 0 < ⟪a i, z - y⟫) ∧
      (∃ j : Fin n, a j ≠ 0 ∧ ⟪a j, z⟫ = b j ∧ 0 < ⟪a j, y - x⟫) := by
  let w := x + (z - y)
  have hfirst : w - x = z - y := by dsimp [w]; abel
  have hsecond : z - w = y - x := by dsimp [w]; abel
  constructor
  · rintro ⟨hxw, hwz⟩
    obtain ⟨i, hai, hiw, hipos⟩ :=
      HirschCircuitLocalization.rowCircuitStep_exists_target_blocking_row
        a b x w hxw
    obtain ⟨j, haj, hjz, hjpos⟩ :=
      HirschCircuitLocalization.rowCircuitStep_exists_target_blocking_row
        a b w z hwz
    refine ⟨hxw.2.1, ⟨i, hai, hiw, ?_⟩, ⟨j, haj, hjz, ?_⟩⟩
    · rw [hfirst] at hipos
      exact hipos
    · rw [hsecond] at hjpos
      exact hjpos
  · rintro ⟨hw, ⟨i, _hai, hi, hipos⟩, ⟨j, _haj, hj, hjpos⟩⟩
    exact rowCircuitStep_swap_of_feasible_and_tight_blockers
      a b x y z hxy hyz hw i j hi hipos hj hjpos

#print axioms rowCircuitStep_iff_target_tight_increasing_row
#print axioms rowCircuitStep_swap_iff_feasible_and_tight_blockers

end HirschCircuit
