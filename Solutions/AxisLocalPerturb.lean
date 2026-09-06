import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 1500000

noncomputable section

namespace HirschAxisLocal

variable {d n : ℕ}

/-- If a direction is orthogonal to every constraint tight at a feasible
point of a finite H-polytope, then sufficiently small perturbations in both
directions remain feasible. -/
lemma exists_two_sided_feasible_perturb
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ Hpoly a b)
    (hy : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, y⟫ = 0) :
    ∃ ε : ℝ, 0 < ε ∧ x - ε • y ∈ Hpoly a b ∧ x + ε • y ∈ Hpoly a b := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun i => ⟪a i, x⟫ ≠ b i)
  by_cases hS : S = ∅
  · refine ⟨1, by norm_num, ?_, ?_⟩
    · intro i
      have ht : ⟪a i, x⟫ = b i := by
        by_contra hne
        have hi : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ i, hne⟩
        rw [hS] at hi
        exact Finset.notMem_empty i hi
      have hz := hy i ht
      simp [inner_sub_right, ht, hz]
    · intro i
      have ht : ⟪a i, x⟫ = b i := by
        by_contra hne
        have hi : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ i, hne⟩
        rw [hS] at hi
        exact Finset.notMem_empty i hi
      have hz := hy i ht
      simp [inner_add_right, ht, hz]
  · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.2 hS
    let δ : ℝ := S.inf' hSne (fun i => b i - ⟪a i, x⟫)
    have hδ : 0 < δ := by
      obtain ⟨iδ, hiδ, hδeq⟩ :=
        S.exists_mem_eq_inf' hSne (fun i => b i - ⟪a i, x⟫)
      have hne : ⟪a iδ, x⟫ ≠ b iδ := (Finset.mem_filter.1 hiδ).2
      have hlt : ⟪a iδ, x⟫ < b iδ := lt_of_le_of_ne (hx iδ) hne
      simpa [δ, hδeq] using sub_pos.2 hlt
    let C : ℝ := ∑ i, |⟪a i, y⟫|
    have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
    let ε : ℝ := δ / (2 * (C + 1))
    have hε : 0 < ε := div_pos hδ (by positivity)
    have hεC : ε * C ≤ δ / 2 := by
      have hle : C ≤ C + 1 := by linarith
      have hmul : ε * C ≤ ε * (C + 1) :=
        mul_le_mul_of_nonneg_left hle hε.le
      have heq : ε * (C + 1) = δ / 2 := by
        dsimp [ε]
        field_simp
      linarith
    have hmem (σ : ℝ) (hσ : |σ| = ε) : x + σ • y ∈ Hpoly a b := by
      intro i
      have hinner : ⟪a i, x + σ • y⟫ =
          ⟪a i, x⟫ + σ * ⟪a i, y⟫ := by
        simp [inner_add_right, inner_smul_right]
      rw [hinner]
      by_cases ht : ⟪a i, x⟫ = b i
      · have hz := hy i ht
        simp [ht, hz]
      · have hiS : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ i, ht⟩
        have hslack : δ ≤ b i - ⟪a i, x⟫ := Finset.inf'_le _ hiS
        have hcoord : |⟪a i, y⟫| ≤ C :=
          Finset.single_le_sum (f := fun j : Fin n => |⟪a j, y⟫|)
            (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
        have habs : |σ * ⟪a i, y⟫| ≤ ε * C := by
          calc
            |σ * ⟪a i, y⟫| = ε * |⟪a i, y⟫| := by simp [abs_mul, hσ]
            _ ≤ ε * C := mul_le_mul_of_nonneg_left hcoord hε.le
        have hraw : σ * ⟪a i, y⟫ ≤ |σ * ⟪a i, y⟫| := le_abs_self _
        linarith
    refine ⟨ε, hε, ?_, ?_⟩
    · simpa [sub_eq_add_neg, neg_smul] using
        hmem (-ε) (by simp [abs_of_pos hε])
    · exact hmem ε (abs_of_pos hε)

end HirschAxisLocal
