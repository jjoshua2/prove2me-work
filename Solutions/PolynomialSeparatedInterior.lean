import Mathlib
import Definitions.Def_Hirsch_model
import Theorems.Thm_Hirsch_nonzero_supporting_row_of_distinct_extremes

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 2500000

noncomputable section

namespace HirschPolynomialAccess

variable {d n : ℕ}

lemma inner_midpoint_eq_avg
    (c : EuclideanSpace ℝ (Fin d))
    (u v : EuclideanSpace ℝ (Fin d)) :
    ⟪c, midpoint ℝ u v⟫ = (⟪c, u⟫ + ⟪c, v⟫) / 2 := by
  rw [midpoint_eq_smul_add (R := ℝ)]
  simp [inner_add_right, inner_smul_right]
  ring

/-- If two vertices share no nonzero defining supporting hyperplane, then the
midpoint of the segment joining them is an interior point of the H-polytope.
Thus every hard target-access instance is automatically full-dimensional,
which in particular makes Todd's full-dimensional hypothesis available. -/
lemma separated_midpoint_mem_interior
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (huv : u ≠ v)
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i) :
    midpoint ℝ u v ∈ interior (Hpoly a b) := by
  classical
  let m : EuclideanSpace ℝ (Fin d) := midpoint ℝ u v
  have huP : u ∈ Hpoly a b := hu.1
  have hvP : v ∈ Hpoly a b := hv.1
  have hstrict : ∀ i, a i ≠ 0 → ⟪a i, m⟫ < b i := by
    intro i hai
    have hui := huP i
    have hvi := hvP i
    have hm : ⟪a i, m⟫ = (⟪a i, u⟫ + ⟪a i, v⟫) / 2 := by
      simpa [m] using inner_midpoint_eq_avg (a i) u v
    rcases hsep i hai with hnu | hnv
    · have hult : ⟪a i, u⟫ < b i := lt_of_le_of_ne hui hnu
      linarith
    · have hvlt : ⟪a i, v⟫ < b i := lt_of_le_of_ne hvi hnv
      linarith
  obtain ⟨i0, hi0, _hi0v⟩ :=
    Hirsch.nonzero_supporting_row_of_distinct_extremes d n a b hbd u hu v hv huv
  let S : Finset (Fin n) := Finset.univ.filter (fun i => a i ≠ 0)
  have hSne : S.Nonempty :=
    ⟨i0, Finset.mem_filter.2 ⟨Finset.mem_univ i0, hi0⟩⟩
  let δ : ℝ := S.inf' hSne (fun i => b i - ⟪a i, m⟫)
  have hδ : 0 < δ := by
    obtain ⟨iδ, hiδ, hδeq⟩ :=
      S.exists_mem_eq_inf' hSne (fun i => b i - ⟪a i, m⟫)
    have hai : a iδ ≠ 0 := (Finset.mem_filter.1 hiδ).2
    have hs := hstrict iδ hai
    simpa [δ, hδeq] using sub_pos.2 hs
  let A : ℝ := ∑ i : Fin n, ‖a i‖
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let ε : ℝ := δ / (2 * (A + 1))
  have hε : 0 < ε := div_pos hδ (by positivity)
  have hεA : ε * A ≤ δ / 2 := by
    have hle : A ≤ A + 1 := by linarith
    have hmul : ε * A ≤ ε * (A + 1) :=
      mul_le_mul_of_nonneg_left hle hε.le
    have heq : ε * (A + 1) = δ / 2 := by
      dsimp [ε]
      field_simp
    linarith
  have hball : Metric.ball m ε ⊆ Hpoly a b := by
    intro x hxball i
    by_cases hai : a i = 0
    · have hbi : 0 ≤ b i := by simpa [hai] using huP i
      simpa [hai] using hbi
    · have hiS : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ i, hai⟩
      have hslack : δ ≤ b i - ⟪a i, m⟫ := Finset.inf'_le _ hiS
      have hnormi : ‖a i‖ ≤ A :=
        Finset.single_le_sum (f := fun j : Fin n => ‖a j‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
      have hdiff : ‖x - m‖ < ε := by
        simpa [Metric.mem_ball, dist_eq_norm] using hxball
      have hni : 0 < ‖a i‖ := norm_pos_iff.mpr hai
      have hprod1 : ‖a i‖ * ‖x - m‖ < ‖a i‖ * ε :=
        mul_lt_mul_of_pos_left hdiff hni
      have hprod2 : ‖a i‖ * ε ≤ A * ε :=
        mul_le_mul_of_nonneg_right hnormi hε.le
      have hsmall : ‖a i‖ * ‖x - m‖ < δ / 2 := by
        have hAε : A * ε ≤ δ / 2 := by simpa [mul_comm] using hεA
        exact hprod1.trans_le (hprod2.trans hAε)
      have habs : |⟪a i, x - m⟫| ≤ ‖a i‖ * ‖x - m‖ :=
        abs_real_inner_le_norm _ _
      have hdev : ⟪a i, x - m⟫ < δ / 2 :=
        lt_of_le_of_lt (le_trans (le_abs_self _) habs) hsmall
      have hdecomp : ⟪a i, x⟫ = ⟪a i, m⟫ + ⟪a i, x - m⟫ := by
        have hx : x = m + (x - m) := by module
        rw [hx, inner_add_right]
      rw [hdecomp]
      linarith
  rw [mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset (Metric.ball_mem_nhds m hε) hball

lemma separated_interior_nonempty
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (huv : u ≠ v)
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i) :
    (interior (Hpoly a b)).Nonempty :=
  ⟨midpoint ℝ u v,
    separated_midpoint_mem_interior a b hbd u v hu hv huv hsep⟩

end HirschPolynomialAccess
