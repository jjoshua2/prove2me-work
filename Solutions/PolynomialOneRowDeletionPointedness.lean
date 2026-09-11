import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace HirschDeletion

/-- Evaluate a vector against every row except one distinguished row. -/
noncomputable def rowMapWithout
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (j : Fin n) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ({i : Fin n // i ≠ j} → ℝ) :=
  { toFun := fun x i => ⟪a i.1, x⟫
    map_add' := by
      intro x y
      funext i
      simp [inner_add_right]
    map_smul' := by
      intro c x
      funext i
      simp [inner_smul_right] }

/-- Deleting any single inequality from a nonempty bounded H-presentation leaves
all remaining row normals spanning the ambient direction space. Equivalently,
the row-evaluation map on all rows except `j` is injective.

Geometric interpretation: the H-polyhedron obtained by deleting one row may
become unbounded, but it cannot acquire lineality. Thus every one-row deletion
outer model is pointed. No irredundancy or strict-feasibility hypothesis is
needed. -/
theorem rowMapWithout_injective_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b)
    (j : Fin n) :
    Function.Injective (rowMapWithout a j) := by
  classical
  intro p q hpq
  by_contra hpqne
  let g : EuclideanSpace ℝ (Fin d) := p - q
  have hg0 : g ≠ 0 := sub_ne_zero.mpr hpqne
  have hker : rowMapWithout a j g = 0 := by
    rw [show g = p - q from rfl, map_sub, hpq, sub_self]
  have hrem : ∀ i : Fin n, i ≠ j → ⟪a i, g⟫ = 0 := by
    intro i hij
    have hi := congrFun hker ⟨i, hij⟩
    simpa [rowMapWithout] using hi
  let s : EuclideanSpace ℝ (Fin d) :=
    if ⟪a j, g⟫ ≤ 0 then g else -g
  have hs0 : s ≠ 0 := by
    by_cases hj : ⟪a j, g⟫ ≤ 0
    · simpa [s, hj] using hg0
    · have hng : -g ≠ 0 := neg_ne_zero.mpr hg0
      simpa [s, hj] using hng
  have hsj : ⟪a j, s⟫ ≤ 0 := by
    by_cases hj : ⟪a j, g⟫ ≤ 0
    · simpa [s, hj]
    · have hjpos : 0 < ⟪a j, g⟫ := lt_of_not_ge hj
      simp [s, hj, inner_neg_right]
      exact hjpos.le
  have hremS : ∀ i : Fin n, i ≠ j → ⟪a i, s⟫ = 0 := by
    intro i hij
    by_cases hj : ⟪a j, g⟫ ≤ 0
    · simpa [s, hj] using hrem i hij
    · simp [s, hj, inner_neg_right, hrem i hij]
  have hline : ∀ t : ℝ, 0 ≤ t → x + t • s ∈ Hpoly a b := by
    intro t ht i
    change ⟪a i, x + t • s⟫ ≤ b i
    rw [inner_add_right, inner_smul_right]
    have hxi := hx i
    by_cases hij : i = j
    · subst i
      have hmul : t * ⟪a j, s⟫ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ht hsj
      linarith
    · rw [hremS i hij, mul_zero, add_zero]
      exact hxi
  obtain ⟨r, hr⟩ := hbd.subset_closedBall x
  have hr0 : 0 ≤ r := by
    have hball0 := Metric.mem_closedBall.mp (hr hx)
    simpa using hball0
  have hsnorm : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  let t : ℝ := (r + 1) / ‖s‖
  have ht : 0 < t := by
    dsimp [t]
    exact div_pos (by linarith) hsnorm
  have hball := Metric.mem_closedBall.mp (hr (hline t ht.le))
  have hdist : dist (x + t • s) x = r + 1 := by
    rw [dist_eq_norm]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    field_simp [ne_of_gt hsnorm]
  rw [hdist] at hball
  linarith

#print axioms rowMapWithout_injective_of_bounded

end HirschDeletion
