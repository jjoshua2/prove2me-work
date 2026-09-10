import Mathlib
import Definitions.Def_Hirsch_circuit_model
import Solutions.PolynomialCommonFace

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 2500000

noncomputable section

namespace HirschPolynomialAccess

variable {d n : ℕ}

/-- A maximal row-circuit augmentation leaving a vertex is already a graph
edge once its common-tight-row carrier is known to lie in the affine line of
the augmentation.  This isolates the geometric content needed to turn the
usual rank-`d-1` active-neutral condition into `Adj`. -/
theorem rowCircuitStep_adj_of_commonFace_line
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hstep : RowCircuitStep a b x y)
    (hline : ∀ z, z ∈ commonFace a b x y →
      ∃ t : ℝ, z = x + t • (y - x)) :
    Adj (Hpoly a b) x y := by
  have hxy : x ≠ y := by
    intro h
    apply hstep.2.2.1.1
    rw [h]
    simp
  have hfaceEq : commonFace a b x y = segment ℝ x y := by
    apply Set.Subset.antisymm
    · intro z hz
      have hzP : z ∈ Hpoly a b := hz.1
      obtain ⟨t, hzt⟩ := hline z hz
      have ht1 : t ≤ 1 := by
        by_contra ht
        have ht' : 1 < t := lt_of_not_ge ht
        exact hstep.2.2.2 t ht' (hzt ▸ hzP)
      have ht0 : 0 ≤ t := by
        by_contra ht
        have htneg : t < 0 := lt_of_not_ge ht
        let α : ℝ := 1 / (1 - t)
        let β : ℝ := -t / (1 - t)
        have hden : 0 < 1 - t := by linarith
        have hα : 0 < α := by
          dsimp [α]
          positivity
        have hβ : 0 < β := by
          dsimp [β]
          exact div_pos (neg_pos.mpr htneg) hden
        have hsum : α + β = 1 := by
          dsimp [α, β]
          field_simp [ne_of_gt hden]
          ring
        have hcoef : α * t + β = 0 := by
          dsimp [α, β]
          field_simp [ne_of_gt hden]
          ring
        have hopen : x ∈ openSegment ℝ z y := by
          refine ⟨α, β, hα, hβ, hsum, ?_⟩
          rw [hzt]
          have hy : y = x + (1 : ℝ) • (y - x) := by module
          rw [hy]
          module
        obtain ⟨_hzx, hyx⟩ := hx.2 z hzP y hstep.2.1 hopen
        exact hxy hyx.symm
      refine ⟨1 - t, t, sub_nonneg.mpr ht1, ht0, by ring, ?_⟩
      rw [hzt]
      module
    · intro z hz
      obtain ⟨α, β, hα, hβ, hsum, hcomb⟩ := hz
      rw [← hcomb]
      refine ⟨?_, ?_⟩
      · intro i
        have hxi := hstep.1 i
        have hyi := hstep.2.1 i
        simp only [inner_add_right, inner_smul_right]
        nlinarith
      · intro i hi
        have hix : ⟪a i, x⟫ = b i := (Finset.mem_filter.1 hi).2.2.1
        have hiy : ⟪a i, y⟫ = b i := (Finset.mem_filter.1 hi).2.2.2
        simp only [inner_add_right, inner_smul_right]
        rw [hix, hiy]
        nlinarith
  have hface : IsExtreme ℝ (Hpoly a b) (segment ℝ x y) := by
    rw [← hfaceEq]
    exact commonFace_isExtreme a b x y
  exact ⟨hxy, hface⟩

#print axioms rowCircuitStep_adj_of_commonFace_line

end HirschPolynomialAccess
