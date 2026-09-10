import Mathlib
import Definitions.Def_Hirsch_model
import Solutions.SingleCutCubeAttachment

open Set Hirsch HirschClip HirschCubeCut

set_option maxHeartbeats 5000000

noncomputable section

/-- An arbitrary single real halfspace cut of the d-cube has full vertex-edge
 diameter at most d+2. No positivity, genericity, integrality, nonemptiness,
 rank, or assumed diameter hypothesis is imposed. -/
theorem solution
    (d : ℕ) (a : Fin d → ℝ) (β : ℝ) :
    Hirsch.DiamLE
      {x : Fin d → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ (∑ i, a i * x i) ≤ β}
      (d + 2) := by
  change DiamLE (Clip a β) (d + 2)
  intro x hx y hy
  obtain ⟨p, hpc, hpP, hpx⟩ := vertex_corner_attachment a β hx
  obtain ⟨q, hqc, hqP, hqy⟩ := vertex_corner_attachment a β hy
  have hwpx : Walk (Clip a β) 1 p x := one_step_walk hpx
  have hwqy : Walk (Clip a β) 1 q y := one_step_walk hqy
  have hwpq := retained_corners_walk a β p q hpP hqP hpc hqc
  have hw := walk_append (walk_append (walk_reverse hwpx) hwpq) hwqy
  have hlen : (1 + d) + 1 = d + 2 := by omega
  simpa only [hlen] using hw

#print axioms solution
