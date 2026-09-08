import Solutions.CircuitSlackTranslation

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped RealInnerProductSpace
open Hirsch

namespace HirschCircuit

/-- Under injectivity of the slack parametrization, every padded slack-coordinate
circuit walk uniquely pulls back to a row-circuit walk in the original H-polytope. -/
theorem slackCircuitWalk_to_rowCircuitWalk
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (rowMap a))
    (L : ℕ) (u v : EuclideanSpace ℝ (Fin d)) :
    SlackCircuitWalk a b L (slack a b u) (slack a b v) →
      RowCircuitWalk a b L u v := by
  classical
  rintro ⟨s, hs0, hsL, hsfeas, hsstep⟩
  let w : ℕ → EuclideanSpace ℝ (Fin d) := fun j =>
    if hj : j ≤ L then Classical.choose (hsfeas j hj).1 else u
  have hwslack : ∀ j (hj : j ≤ L), slack a b (w j) = s j := by
    intro j hj
    dsimp [w]
    rw [dif_pos hj]
    exact (Classical.choose_spec (hsfeas j hj).1).symm
  have hsinj : Function.Injective (slack a b) :=
    slack_injective_of_rowMap_injective a b hinj
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · apply hsinj
    rw [hwslack 0 (Nat.zero_le L), hs0]
  · apply hsinj
    rw [hwslack L le_rfl, hsL]
  · intro j hj
    apply (slack_mem_SlackPoly_iff a b (w j)).mp
    rw [hwslack j hj]
    exact hsfeas j hj
  · intro j hj
    have hjL : j ≤ L := Nat.le_of_lt hj
    have hj1L : j + 1 ≤ L := Nat.succ_le_iff.mpr hj
    rcases hsstep j hj with hstay | hmove
    · left
      apply hsinj
      rw [hwslack j hjL, hwslack (j + 1) hj1L, hstay]
    · right
      apply (rowCircuitStep_iff_slackCircuitStep a b hinj (w j) (w (j + 1))).mpr
      rw [hwslack j hjL, hwslack (j + 1) hj1L]
      exact hmove

/-- Exact equivalence of the original and slack-coordinate circuit-walk notions
once boundedness has supplied injectivity. -/
theorem rowCircuitWalk_iff_slackCircuitWalk
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (rowMap a))
    (L : ℕ) (u v : EuclideanSpace ℝ (Fin d)) :
    RowCircuitWalk a b L u v ↔
      SlackCircuitWalk a b L (slack a b u) (slack a b v) := by
  constructor
  · exact rowCircuitWalk_to_slackCircuitWalk a b hinj L u v
  · exact slackCircuitWalk_to_rowCircuitWalk a b hinj L u v

#print axioms slackCircuitWalk_to_rowCircuitWalk
#print axioms rowCircuitWalk_iff_slackCircuitWalk

end HirschCircuit
