import Mathlib
import Solutions.PolynomialCircuitCheckpointLocalization

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 5000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

variable {d n : ℕ}

/-- A maximal feasible circuit step must finish on a genuinely new blocking
row: some row tight at the destination increases strictly along the step.
Neither endpoint is assumed to be a vertex. -/
theorem rowCircuitStep_exists_target_blocking_row
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hstep : RowCircuitStep a b x y) :
    ∃ i : Fin n, a i ≠ 0 ∧ ⟪a i, y⟫ = b i ∧ 0 < ⟪a i, y - x⟫ := by
  classical
  let g := y - x
  by_contra hnone
  push_neg at hnone
  have htight_zero : ∀ i : Fin n, ⟪a i, y⟫ = b i → ⟪a i, g⟫ = 0 := by
    intro i hiy
    have hxle := hstep.1 i
    have hnonneg : 0 ≤ ⟪a i, g⟫ := by
      dsimp [g]
      rw [inner_sub_right, hiy]
      linarith
    have hnpos : ¬ 0 < ⟪a i, g⟫ := by
      intro hpos
      have hai : a i ≠ 0 := by
        intro hai
        rw [hai, inner_zero_left] at hpos
        linarith
      exact (hnone i hai hiy) hpos
    exact le_antisymm (le_of_not_gt hnpos) hnonneg
  have hlocal : ∀ i : Fin n, ∃ t : ℝ,
      0 < t ∧ t * |⟪a i, g⟫| ≤ b i - ⟪a i, y⟫ := by
    intro i
    by_cases hi : ⟪a i, y⟫ = b i
    · refine ⟨1, zero_lt_one, ?_⟩
      rw [htight_zero i hi, abs_zero, mul_zero, hi, sub_self]
    · have hs : 0 < b i - ⟪a i, y⟫ :=
        sub_pos.mpr (lt_of_le_of_ne (hstep.2.1 i) hi)
      have hden : 0 < |⟪a i, g⟫| + 1 := by positivity
      let t : ℝ := (b i - ⟪a i, y⟫) / (|⟪a i, g⟫| + 1)
      have ht : 0 < t := div_pos hs hden
      have hprod : t * (|⟪a i, g⟫| + 1) = b i - ⟪a i, y⟫ := by
        dsimp [t]
        exact div_mul_cancel₀ _ (ne_of_gt hden)
      exact ⟨t, ht, by nlinarith⟩
  choose e hepos hebound using hlocal
  have huniform : ∀ S : Finset (Fin n), ∃ t : ℝ,
      0 < t ∧ ∀ i ∈ S, t ≤ e i := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i S hi ih =>
      obtain ⟨t, ht, hti⟩ := ih
      refine ⟨min (e i) t, lt_min (hepos i) ht, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hjS
      · subst j
        exact min_le_left _ _
      · exact (min_le_right _ _).trans (hti j hjS)
  obtain ⟨t, ht, hte⟩ := huniform Finset.univ
  have hbudget : ∀ i, t * |⟪a i, g⟫| ≤ b i - ⟪a i, y⟫ := by
    intro i
    exact (mul_le_mul_of_nonneg_right (hte i (Finset.mem_univ i))
      (abs_nonneg _)).trans (hebound i)
  have hforward : y + t • g ∈ Hpoly a b := by
    intro i
    have hmul := mul_le_mul_of_nonneg_left (le_abs_self ⟪a i, g⟫) ht.le
    rw [inner_add_right, inner_smul_right]
    linarith [hbudget i]
  have hscale : 1 < (1 + t : ℝ) := by linarith
  apply hstep.2.2.2 (1 + t) hscale
  have heq : x + (1 + t) • (y - x) = y + t • g := by
    dsimp [g]
    module
  rw [heq]
  exact hforward

/-- The destination self-carrier of a maximal circuit step is a strict
subspace of the common carrier of the step. Maximality, rather than endpoint
vertexhood, supplies the strictness. -/
theorem commonDirection_target_self_lt_of_rowCircuitStep
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hstep : RowCircuitStep a b x y) :
    commonDirection a b y y < commonDirection a b x y := by
  classical
  obtain ⟨i0, hi0a, hi0y, hi0pos⟩ :=
    rowCircuitStep_exists_target_blocking_row a b x y hstep
  have hle : commonDirection a b y y ≤ commonDirection a b x y := by
    intro q hq
    change rowEvalMap a (commonSourceRows a b x y) q = 0
    have hself : rowEvalMap a (commonSourceRows a b y y) q = 0 :=
      LinearMap.mem_ker.1 hq
    funext ii
    have hi := (Finset.mem_filter.1 ii.2).2
    have hiYY : ii.1 ∈ commonSourceRows a b y y := by
      simp [commonSourceRows, hi.1, hi.2.2]
    exact congrFun hself ⟨ii.1, hiYY⟩
  have hgxy : y - x ∈ commonDirection a b x y := by
    change rowEvalMap a (commonSourceRows a b x y) (y - x) = 0
    funext ii
    have hi := (Finset.mem_filter.1 ii.2).2
    change ⟪a ii.1, y - x⟫ = 0
    rw [inner_sub_right, hi.2.2, hi.2.1]
    ring
  have hgnot : y - x ∉ commonDirection a b y y := by
    intro hg
    have hker : rowEvalMap a (commonSourceRows a b y y) (y - x) = 0 :=
      LinearMap.mem_ker.1 hg
    have hiYY : i0 ∈ commonSourceRows a b y y := by
      simp [commonSourceRows, hi0a, hi0y]
    have hcoord := congrFun hker ⟨i0, hiYY⟩
    change ⟪a i0, y - x⟫ = 0 at hcoord
    linarith
  refine lt_of_le_of_ne hle ?_
  intro heq
  apply hgnot
  rw [heq]
  exact hgxy

/-- Every nontrivial maximal circuit step strictly lowers carrier dimension
when the destination is viewed against itself. -/
theorem rowCircuitStep_target_commonFaceDim_lt
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hstep : RowCircuitStep a b x y) :
    commonFaceDim a b y y < commonFaceDim a b x y := by
  exact Submodule.finrank_lt_finrank_of_lt
    (commonDirection_target_self_lt_of_rowCircuitStep a b x y hstep)

/-- Maximality removes the target-nullity term from nonvertex circuit
localization. If `z` is any reference vertex of the same H-polyhedron, a
maximal circuit step `x -> y` satisfies

    dim F(x,y) + d <= n + dim F(x,x).

Thus carrier dimension is controlled by ambient row excess plus the source
checkpoint's own face dimension, even though `x` and `y` need not be vertices. -/
theorem rowCircuitStep_commonFaceDim_source_bound
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (z x y : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ extremePoints ℝ (Hpoly a b))
    (hstep : RowCircuitStep a b x y) :
    commonFaceDim a b x y + d ≤ n + commonFaceDim a b x x := by
  have hloc := rowCircuit_commonFaceDim_checkpoint_localization
    a b z x y hz hstep.2.2.1
  have hdrop := rowCircuitStep_target_commonFaceDim_lt a b x y hstep
  omega

/-- Equivalent progress form: the destination checkpoint's own-face
dimension can increase by at most the ambient row excess minus one per
nontrivial maximal circuit step. -/
theorem rowCircuitStep_target_commonFaceDim_progress
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (z x y : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ extremePoints ℝ (Hpoly a b))
    (hstep : RowCircuitStep a b x y) :
    commonFaceDim a b y y + d + 1 ≤ n + commonFaceDim a b x x := by
  have hcarrier := rowCircuitStep_commonFaceDim_source_bound a b z x y hz hstep
  have hdrop := rowCircuitStep_target_commonFaceDim_lt a b x y hstep
  omega

#print axioms rowCircuitStep_exists_target_blocking_row
#print axioms commonDirection_target_self_lt_of_rowCircuitStep
#print axioms rowCircuitStep_target_commonFaceDim_lt
#print axioms rowCircuitStep_commonFaceDim_source_bound
#print axioms rowCircuitStep_target_commonFaceDim_progress

end HirschCircuitLocalization
