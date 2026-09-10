import Mathlib
import Definitions.Def_Hirsch_model
import Solutions.PolynomialVertexSpan

open scoped RealInnerProductSpace
open Set Hirsch HirschPolynomialAccess

set_option maxHeartbeats 3000000

noncomputable section

namespace HirschExposure

/-- The sum of rows active at a vertex exposes precisely that vertex.
A distinct feasible point ensures the exposing normal is nonzero. Boundedness
and irredundancy are unnecessary. -/
theorem exposing_row_from_active_sum
    (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b)
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (huv : u ≠ v) :
    ∃ (c : EuclideanSpace ℝ (Fin d)) (β : ℝ),
      c ≠ 0 ∧ ⟪c, v⟫ = β ∧ ⟪c, u⟫ < β ∧
      (∀ x ∈ Hpoly a b, ⟪c, x⟫ ≤ β) ∧
      (∀ x ∈ Hpoly a b, ⟪c, x⟫ = β ↔ x = v) := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun i => ⟪a i, v⟫ = b i)
  let c : EuclideanSpace ℝ (Fin d) := ∑ i ∈ S, a i
  let β : ℝ := ∑ i ∈ S, b i
  have hcv : ⟪c, v⟫ = β := by
    dsimp [c, β]
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    exact (Finset.mem_filter.1 hi).2
  have hle : ∀ x ∈ Hpoly a b, ⟪c, x⟫ ≤ β := by
    intro x hx
    dsimp [c, β]
    rw [sum_inner]
    exact Finset.sum_le_sum (fun i _ => hx i)
  have heq : ∀ x ∈ Hpoly a b, ⟪c, x⟫ = β ↔ x = v := by
    intro x hx
    constructor
    · intro hcx
      have hsum : (∑ i ∈ S, (b i - ⟪a i, x⟫)) = 0 := by
        rw [Finset.sum_sub_distrib]
        have hsuminner : (∑ i ∈ S, ⟪a i, x⟫) = ⟪c, x⟫ := by
          dsimp [c]
          rw [sum_inner]
        rw [hsuminner]
        exact sub_eq_zero.mpr hcx.symm
      have hall : ∀ i, ⟪a i, v⟫ = b i → ⟪a i, x⟫ = b i := by
        intro i hit
        have hiS : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ i, hit⟩
        have hi_le : b i - ⟪a i, x⟫ ≤ ∑ j ∈ S, (b j - ⟪a j, x⟫) :=
          Finset.single_le_sum (fun j _ => sub_nonneg.mpr (hx j)) hiS
        rw [hsum] at hi_le
        linarith [hx i]
      have horth : ∀ i, ⟪a i, v⟫ = b i → ⟪a i, x - v⟫ = 0 := by
        intro i hit
        rw [inner_sub_right, hall i hit, hit, sub_self]
      exact sub_eq_zero.mp (vertex_tight_rows_span_checked d n a b v hv (x - v) horth)
    · intro h
      rw [h]
      exact hcv
  have hc : c ≠ 0 := by
    intro hc0
    have hcu : ⟪c, u⟫ = β := by
      have hb0 : β = 0 := by simpa only [hc0, inner_zero_left] using hcv.symm
      rw [hc0, inner_zero_left, hb0]
    exact huv ((heq u hu).1 hcu)
  have hult : ⟪c, u⟫ < β :=
    lt_of_le_of_ne (hle u hu) (fun h => huv ((heq u hu).1 h))
  exact ⟨c, β, hc, hcv, hult, hle, heq⟩

#print axioms exposing_row_from_active_sum

end HirschExposure
