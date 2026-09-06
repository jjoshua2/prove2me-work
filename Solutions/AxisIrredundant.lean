import Mathlib
import Solutions.AxisProductScratch

open scoped RealInnerProductSpace
open Set WithLp EuclideanSpace Hirsch

noncomputable section

namespace HirschAxisIrredundant

variable {d n : ℕ}

/-- In a normalized description `c_i · x ≤ 1`, every nonredundant row is a
genuine facet: there is a point on that row which satisfies every other row
strictly.  The proof walks from the strict interior point `0` toward a witness
that the row is not implied by the others. -/
lemma facet_witness_of_not_redundant
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n)
    (hnr : ¬ HirschAxisProduct.RowRedundant c (fun _ => (1 : ℝ)) r) :
    ∃ x : EuclideanSpace ℝ (Fin d),
      ⟪c r, x⟫ = 1 ∧ ∀ i, i ≠ r → ⟪c i, x⟫ < 1 := by
  rw [HirschAxisProduct.RowRedundant] at hnr
  push_neg at hnr
  obtain ⟨z, hzother, hzr⟩ := hnr
  have hzrgt : 1 < ⟪c r, z⟫ := lt_of_not_ge hzr
  let λ : ℝ := (⟪c r, z⟫)⁻¹
  have hcrpos : 0 < ⟪c r, z⟫ := lt_trans zero_lt_one hzrgt
  have hλpos : 0 < λ := inv_pos.2 hcrpos
  have hλlt : λ < 1 := by
    rw [inv_lt_one₀ hcrpos]
    exact hzrgt
  let x : EuclideanSpace ℝ (Fin d) := λ • z
  refine ⟨x, ?_, ?_⟩
  · simp [x, λ, inner_smul_right]
    exact inv_mul_cancel₀ hcrpos.ne'
  · intro i hir
    have hiz := hzother i hir
    have hmul := mul_le_mul_of_nonneg_left hiz hλpos.le
    have hlt : λ * (1 : ℝ) < 1 := by simpa using hλlt
    rw [show ⟪c i, x⟫ = λ * ⟪c i, z⟫ by simp [x, inner_smul_right]]
    linarith

/-- Consequently a nonredundant normalized row cuts out exactly the set where
that inequality is tight, with a witness in the relative interior of that
codimension-one face. -/
lemma facet_face_nonempty_relative
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n)
    (hnr : ¬ HirschAxisProduct.RowRedundant c (fun _ => (1 : ℝ)) r) :
    ∃ x ∈ Hpoly c (fun _ => (1 : ℝ)),
      ⟪c r, x⟫ = 1 ∧ ∀ i, i ≠ r → ⟪c i, x⟫ < 1 := by
  obtain ⟨x, hr, hother⟩ := facet_witness_of_not_redundant c r hnr
  refine ⟨x, ?_, hr, hother⟩
  intro i
  by_cases hir : i = r
  · subst i
    exact hr.le
  · exact (hother i hir).le

end HirschAxisIrredundant
