import Solutions.PolynomialHpolyHorizonInward

/-! Follow the one-dimensional inward horizon direction until the first old
H-inequality becomes tight. The first-hit point is an old H-polyhedron vertex. -/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section
namespace HirschHpolyCap

variable {d n : ℕ}

/-- A genuinely new horizon vertex admits a positive first-hit time along an
inward old-active-kernel direction. The result exposes one attaining old row,
so the segment can subsequently be certified as an actual cap edge. -/
theorem new_horizon_first_hit_old_vertex
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (cappedHpoly a b T))
    (horizon : ⟪capNormal a, x⟫ = T)
    (hnotold : x ∉ extremePoints ℝ (Hpoly a b)) :
    ∃ r : EuclideanSpace ℝ (Fin d), ∃ t : ℝ, ∃ j : Fin n,
      r ≠ 0 ∧ 0 < t ∧
      (∀ i, ⟪a i, x⟫ = b i → ⟪a i, r⟫ = 0) ∧
      ⟪capNormal a, r⟫ < 0 ∧
      0 < ⟪a j, r⟫ ∧
      ⟪a j, x + t • r⟫ = b j ∧
      x + t • r ∈ extremePoints ℝ (Hpoly a b) ∧
      ⟪capNormal a, x + t • r⟫ < T := by
  classical
  obtain ⟨r, i0, hr0, hrActive, hrCap, hi0, hxi0⟩ :=
    exists_increasing_inactive_row_at_new_horizon a b T x hx horizon hnotold
  let S : Finset (Fin n) := Finset.univ.filter (fun i => 0 < ⟪a i, r⟫)
  have hi0S : i0 ∈ S := by simp [S, hi0]
  have hS : S.Nonempty := ⟨i0, hi0S⟩
  let τ : Fin n → ℝ := fun i => (b i - ⟪a i, x⟫) / ⟪a i, r⟫
  let times : Finset ℝ := S.image τ
  have htimes : times.Nonempty := Finset.image_nonempty.mpr hS
  let t : ℝ := times.min' htimes
  have htmem : t ∈ times := Finset.min'_mem times htimes
  obtain ⟨j, hjS, hjt⟩ := Finset.mem_image.mp htmem
  have hjpos : 0 < ⟪a j, r⟫ := by simpa [S] using hjS
  have hjstrict : ⟪a j, x⟫ < b j := by
    have hle := hx.1.1 j
    exact lt_of_le_of_ne hle (fun heq => by
      have hz := hrActive j heq
      linarith)
  have hτj : 0 < τ j := div_pos (sub_pos.mpr hjstrict) hjpos
  have htpos : 0 < t := by
    rw [← hjt]
    exact hτj
  have htle : ∀ i ∈ S, t ≤ τ i := by
    intro i hiS
    exact Finset.min'_le times (τ i) (Finset.mem_image_of_mem τ hiS)
  let y := x + t • r
  have hyH : y ∈ Hpoly a b := by
    intro i
    change ⟪a i, x + t • r⟫ ≤ b i
    rw [inner_add_right, inner_smul_right]
    by_cases hipos : 0 < ⟪a i, r⟫
    · have hiS : i ∈ S := by simp [S, hipos]
      have hti := htle i hiS
      dsimp [τ] at hti
      have hmul := (le_div_iff₀ hipos).mp hti
      linarith
    · have hir : ⟪a i, r⟫ ≤ 0 := le_of_not_gt hipos
      have hprod : t * ⟪a i, r⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos htpos.le hir
      linarith [hx.1.1 i]
  have hjhit : ⟪a j, y⟫ = b j := by
    change ⟪a j, x + t • r⟫ = b j
    rw [inner_add_right, inner_smul_right]
    have htj : t = τ j := by exact hjt.symm
    rw [htj]
    dsimp [τ]
    field_simp
    ring
  have hOldTightAtY : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, y⟫ = b i := by
    intro i hi
    change ⟪a i, x + t • r⟫ = b i
    rw [inner_add_right, inner_smul_right, hrActive i hi, mul_zero, add_zero, hi]
  have hyExtreme : y ∈ extremePoints ℝ (Hpoly a b) := by
    apply extreme_of_tight_rows_separate a b y hyH
    intro z hz
    apply horizon_old_active_plus_row_separate a b T x hx horizon r hr0 hrActive j hjpos z
    · intro i hi
      exact hz i (hOldTightAtY i hi)
    · exact hz j hjhit
  have hyCap : ⟪capNormal a, y⟫ < T := by
    change ⟪capNormal a, x + t • r⟫ < T
    rw [inner_add_right, inner_smul_right, horizon]
    have : t * ⟪capNormal a, r⟫ < 0 := mul_neg_of_pos_of_neg htpos hrCap
    linarith
  exact ⟨r, t, j, hr0, htpos, hrActive, hrCap, hjpos, hjhit,
    hyExtreme, hyCap⟩

#print axioms new_horizon_first_hit_old_vertex

end HirschHpolyCap
