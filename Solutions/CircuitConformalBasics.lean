import Solutions.CircuitSlackTranslation

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped RealInnerProductSpace
open Hirsch

namespace HirschCircuit

/-- Natura's conformal partial order: common closed orthant and bounded magnitudes. -/
def ConformalTo {n : ℕ} (x y : Fin n → ℝ) : Prop :=
  ∀ i, 0 ≤ x i * y i ∧ |x i| ≤ |y i|
notation:50 x " ⊑ᶜ " y => ConformalTo x y

theorem conformalTo_refl {n : ℕ} (x : Fin n → ℝ) : x ⊑ᶜ x := by
  intro i
  exact ⟨mul_self_nonneg _, le_rfl⟩

theorem conformalTo_zero {n : ℕ} (x : Fin n → ℝ) :
    (0 : Fin n → ℝ) ⊑ᶜ x := by
  intro i
  simp

theorem conformalTo_support_subset {n : ℕ} {x y : Fin n → ℝ}
    (hxy : x ⊑ᶜ y) : Function.support x ⊆ Function.support y := by
  intro i hix
  simp only [Function.mem_support] at hix ⊢
  intro hy0
  have habs := (hxy i).2
  rw [hy0, abs_zero] at habs
  exact hix (abs_eq_zero.mp (le_antisymm habs (abs_nonneg _)))

theorem conformalTo_eq_zero_of_right_eq_zero {n : ℕ} {x y : Fin n → ℝ}
    (hxy : x ⊑ᶜ y) {i : Fin n} (hy : y i = 0) : x i = 0 := by
  have habs := (hxy i).2
  rw [hy, abs_zero] at habs
  exact abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))

theorem conformalTo_smul {n : ℕ} {x y : Fin n → ℝ}
    (hxy : x ⊑ᶜ y) {c : ℝ} (_hc : 0 ≤ c) :
    (c • x) ⊑ᶜ (c • y) := by
  intro i
  constructor
  · simp only [Pi.smul_apply, smul_eq_mul]
    nlinarith [(hxy i).1, sq_nonneg c]
  · simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hxy i).2 (abs_nonneg c)

theorem conformalTo_coord_nonneg_of_right_nonneg {n : ℕ}
    {x y : Fin n → ℝ} (hxy : x ⊑ᶜ y) {i : Fin n} (hy : 0 ≤ y i) :
    0 ≤ x i := by
  rcases lt_or_eq_of_le hy with hypos | hy0
  · have hsign := (hxy i).1
    nlinarith
  · rw [conformalTo_eq_zero_of_right_eq_zero hxy hy0.symm]

theorem conformalTo_coord_nonpos_of_right_nonpos {n : ℕ}
    {x y : Fin n → ℝ} (hxy : x ⊑ᶜ y) {i : Fin n} (hy : y i ≤ 0) :
    x i ≤ 0 := by
  rcases lt_or_eq_of_le hy with hyneg | hy0
  · have hsign := (hxy i).1
    nlinarith
  · rw [conformalTo_eq_zero_of_right_eq_zero hxy hy0]

/-- Subtracting a conformal piece preserves the orthant and magnitude bound. -/
theorem conformalTo_sub_right {n : ℕ} {x y : Fin n → ℝ}
    (hxy : x ⊑ᶜ y) : (y - x) ⊑ᶜ y := by
  intro i
  rcases le_total 0 (y i) with hy | hy
  · have hx0 := conformalTo_coord_nonneg_of_right_nonneg hxy hy
    have habs := (hxy i).2
    rw [abs_of_nonneg hx0, abs_of_nonneg hy] at habs
    have hres0 : 0 ≤ y i - x i := by linarith
    constructor
    · exact mul_nonneg hres0 hy
    · change |y i - x i| ≤ |y i|
      rw [abs_of_nonneg hres0, abs_of_nonneg hy]
      linarith
  · have hx0 := conformalTo_coord_nonpos_of_right_nonpos hxy hy
    have habs := (hxy i).2
    rw [abs_of_nonpos hx0, abs_of_nonpos hy] at habs
    have hres0 : y i - x i ≤ 0 := by linarith
    constructor
    · exact mul_nonneg_of_nonpos_of_nonpos hres0 hy
    · change |y i - x i| ≤ |y i|
      rw [abs_of_nonpos hres0, abs_of_nonpos hy]
      linarith

theorem abs_add_residual_eq_abs {n : ℕ} {x y : Fin n → ℝ}
    (hxy : x ⊑ᶜ y) (i : Fin n) :
    |x i| + |y i - x i| = |y i| := by
  rcases le_total 0 (y i) with hy | hy
  · have hx0 := conformalTo_coord_nonneg_of_right_nonneg hxy hy
    have habs := (hxy i).2
    rw [abs_of_nonneg hx0, abs_of_nonneg hy] at habs
    have hres0 : 0 ≤ y i - x i := by linarith
    rw [abs_of_nonneg hx0, abs_of_nonneg hres0, abs_of_nonneg hy]
    ring
  · have hx0 := conformalTo_coord_nonpos_of_right_nonpos hxy hy
    have habs := (hxy i).2
    rw [abs_of_nonpos hx0, abs_of_nonpos hy] at habs
    have hres0 : y i - x i ≤ 0 := by linarith
    rw [abs_of_nonpos hx0, abs_of_nonpos hres0, abs_of_nonpos hy]
    ring

/-- Weighted absolute-value potential; zero weights omit coordinates. -/
noncomputable def weightedL1 {n : ℕ} (w x : Fin n → ℝ) : ℝ :=
  ∑ i, w i * |x i|

theorem weightedL1_conformal_split {n : ℕ} (w : Fin n → ℝ)
    {x y : Fin n → ℝ} (hxy : x ⊑ᶜ y) :
    weightedL1 w y = weightedL1 w x + weightedL1 w (y - x) := by
  simp only [weightedL1, ← Finset.sum_add_distrib, Pi.sub_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_add, abs_add_residual_eq_abs hxy i]

theorem support_smul_eq {n : ℕ} (z : Fin n → ℝ) {c : ℝ} (hc : c ≠ 0) :
    Function.support (c • z) = Function.support z := by
  ext i
  simp [Function.mem_support, hc]

theorem isElementaryIn_smul {n : ℕ} (K : Submodule ℝ (Fin n → ℝ))
    {z : Fin n → ℝ} (hz : IsElementaryIn K z) {c : ℝ} (hc : c ≠ 0) :
    IsElementaryIn K (c • z) := by
  rcases hz with ⟨hz0, hzK, hmin⟩
  refine ⟨?_, K.smul_mem c hzK, ?_⟩
  · intro hcz
    apply hz0
    have := congrArg (fun q : Fin n → ℝ => c⁻¹ • q) hcz
    simpa [hc] using this
  · intro q hq0 hqK hqsub
    rw [support_smul_eq z hc] at hqsub ⊢
    exact hmin q hq0 hqK hqsub

#print axioms conformalTo_sub_right
#print axioms weightedL1_conformal_split
#print axioms isElementaryIn_smul
end HirschCircuit
