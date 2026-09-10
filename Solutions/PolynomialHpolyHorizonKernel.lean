import Solutions.PolynomialHpolyVertexConverse

/-! Local linear structure at a new horizon vertex of the canonical H-polyhedron
cap. The old active rows have a common kernel of dimension at most one, because
adding the active cap functional makes the point extreme. -/

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section
namespace HirschHpolyCap

variable {d n : ℕ}

/-- At a horizon vertex, a direction annihilating every active old row and the
cap normal must be zero. -/
lemma horizon_active_rows_separate
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (cappedHpoly a b T))
    (horizon : ⟪capNormal a, x⟫ = T)
    (y : EuclideanSpace ℝ (Fin d))
    (hold : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, y⟫ = 0)
    (hcap : ⟪capNormal a, y⟫ = 0) :
    y = 0 := by
  classical
  have hlocal : ∀ i : Fin n, ∃ t : ℝ,
      0 < t ∧ t * |⟪a i, y⟫| ≤ b i - ⟪a i, x⟫ := by
    intro i
    by_cases hi : ⟪a i, x⟫ = b i
    · refine ⟨1, zero_lt_one, ?_⟩
      rw [hold i hi, abs_zero, mul_zero, hi, sub_self]
    · have hs : 0 < b i - ⟪a i, x⟫ :=
        sub_pos.mpr (lt_of_le_of_ne (hx.1.1 i) hi)
      have hd : 0 < |⟪a i, y⟫| + 1 := by positivity
      let t : ℝ := (b i - ⟪a i, x⟫) / (|⟪a i, y⟫| + 1)
      have ht : 0 < t := div_pos hs hd
      have hprod : t * (|⟪a i, y⟫| + 1) = b i - ⟪a i, x⟫ := by
        dsimp [t]
        exact div_mul_cancel₀ _ (ne_of_gt hd)
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
  have hbudget : ∀ i, t * |⟪a i, y⟫| ≤ b i - ⟪a i, x⟫ := by
    intro i
    exact (mul_le_mul_of_nonneg_right (hte i (Finset.mem_univ i))
      (abs_nonneg _)).trans (hebound i)
  have hpH : x + t • y ∈ Hpoly a b := by
    intro i
    have hmul := mul_le_mul_of_nonneg_left (le_abs_self ⟪a i, y⟫) ht.le
    rw [inner_add_right, inner_smul_right]
    linarith [hbudget i]
  have hmH : x - t • y ∈ Hpoly a b := by
    intro i
    have hmul := mul_le_mul_of_nonneg_left (neg_le_abs ⟪a i, y⟫) ht.le
    rw [mul_neg] at hmul
    rw [inner_sub_right, inner_smul_right]
    linarith [hbudget i]
  have hpCap : ⟪capNormal a, x + t • y⟫ ≤ T := by
    rw [inner_add_right, inner_smul_right, hcap, mul_zero, add_zero, horizon]
  have hmCap : ⟪capNormal a, x - t • y⟫ ≤ T := by
    rw [inner_sub_right, inner_smul_right, hcap, mul_zero, sub_zero, horizon]
  have hp : x + t • y ∈ cappedHpoly a b T := ⟨hpH, hpCap⟩
  have hm : x - t • y ∈ cappedHpoly a b T := ⟨hmH, hmCap⟩
  have hmid : x ∈ openSegment ℝ (x + t • y) (x - t • y) := by
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num,
      by norm_num, ?_⟩
    module
  have hpeq : x + t • y = x := hx.2 hp hm hmid
  have hty : t • y = 0 := by
    have h := congrArg (fun z => z - x) hpeq
    simpa using h
  exact (smul_eq_zero.mp hty).resolve_left (ne_of_gt ht)

/-- Any chosen nonzero old-active kernel direction spans the whole old-active
kernel at a horizon vertex. -/
lemma horizon_old_active_kernel_spanned
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (cappedHpoly a b T))
    (horizon : ⟪capNormal a, x⟫ = T)
    (r : EuclideanSpace ℝ (Fin d)) (hr0 : r ≠ 0)
    (hr : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, r⟫ = 0)
    (y : EuclideanSpace ℝ (Fin d))
    (hy : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, y⟫ = 0) :
    ∃ c : ℝ, y = c • r := by
  have hcr : ⟪capNormal a, r⟫ ≠ 0 := by
    intro hz
    exact hr0 (horizon_active_rows_separate a b T x hx horizon r hr hz)
  let c : ℝ := ⟪capNormal a, y⟫ / ⟪capNormal a, r⟫
  have hwOld : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, y - c • r⟫ = 0 := by
    intro i hi
    rw [inner_sub_right, inner_smul_right, hy i hi, hr i hi, mul_zero, sub_zero]
  have hwCap : ⟪capNormal a, y - c • r⟫ = 0 := by
    rw [inner_sub_right, inner_smul_right]
    dsimp [c]
    field_simp
    ring
  have hw := horizon_active_rows_separate a b T x hx horizon (y - c • r) hwOld hwCap
  exact ⟨c, sub_eq_zero.mp hw⟩

/-- Once one additional old row is nonzero on the one-dimensional horizon
kernel, adjoining that row to the old active rows separates all directions. -/
lemma horizon_old_active_plus_row_separate
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (cappedHpoly a b T))
    (horizon : ⟪capNormal a, x⟫ = T)
    (r : EuclideanSpace ℝ (Fin d)) (hr0 : r ≠ 0)
    (hr : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, r⟫ = 0)
    (j : Fin n) (hrj : ⟪a j, r⟫ ≠ 0)
    (y : EuclideanSpace ℝ (Fin d))
    (hy : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, y⟫ = 0)
    (hyj : ⟪a j, y⟫ = 0) :
    y = 0 := by
  obtain ⟨c, rfl⟩ := horizon_old_active_kernel_spanned a b T x hx horizon r hr0 hr y hy
  have hc : c = 0 := by
    rw [inner_smul_right] at hyj
    exact (mul_eq_zero.mp hyj).resolve_right hrj
  simp [hc]

#print axioms horizon_active_rows_separate
#print axioms horizon_old_active_kernel_spanned
#print axioms horizon_old_active_plus_row_separate

end HirschHpolyCap
