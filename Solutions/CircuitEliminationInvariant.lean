import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace HirschCircuit

/-- A scalar conformal piece lies between zero and the full displacement. -/
def ScalarConformalPiece (g delta : ℝ) : Prop :=
  (0 ≤ g ∧ g ≤ delta) ∨ (delta ≤ g ∧ g ≤ 0)

theorem scalarConformalPiece_of_sign_abs
    (g delta : ℝ) (hsign : 0 ≤ g * delta) (habs : |g| ≤ |delta|) :
    ScalarConformalPiece g delta := by
  rcases le_total 0 delta with hd | hd
  · by_cases hd0 : delta = 0
    · have hg : g = 0 := by
        apply abs_eq_zero.mp
        apply le_antisymm
        · simpa only [hd0, abs_zero] using habs
        · exact abs_nonneg g
      left
      simp [hg, hd0]
    · have hdp : 0 < delta := by
        rcases lt_or_eq_of_le hd with hp | he
        · exact hp
        · exact (hd0 he.symm).elim
      have hg : 0 ≤ g := by
        by_contra hn
        have hn' : g < 0 := lt_of_not_ge hn
        have hneg := mul_neg_of_neg_of_pos hn' hdp
        linarith
      left
      refine ⟨hg, ?_⟩
      simpa only [abs_of_nonneg hg, abs_of_nonneg hd] using habs
  · by_cases hd0 : delta = 0
    · have hg : g = 0 := by
        apply abs_eq_zero.mp
        apply le_antisymm
        · simpa only [hd0, abs_zero] using habs
        · exact abs_nonneg g
      right
      simp [hg, hd0]
    · have hdn : delta < 0 := lt_of_le_of_ne hd hd0
      have hg : g ≤ 0 := by
        by_contra hn
        have hn' : 0 < g := lt_of_not_ge hn
        have hneg := mul_neg_of_pos_of_neg hn' hdn
        linarith
      right
      refine ⟨?_, hg⟩
      rw [abs_of_nonpos hg, abs_of_nonpos hd] at habs
      linarith

/-- Bound the full scaled displacement before considering a conformal piece.
This is purely scalar algebra; no circuit, rank, or vertex assumption occurs. -/
theorem elimination_full_displacement_bounds
    (M v x r lam eta : ℝ)
    (hM : 2 ≤ M) (hv : 0 ≤ v) (hx : 0 ≤ x) (hr : 0 ≤ r)
    (hxM : x ≤ M * v) (hrM : r ≤ M * v)
    (hlam : 0 ≤ lam) (heta : 0 ≤ eta)
    (hlamM : M * lam ≤ 1 / 2) (hetaM : M * eta ≤ lam) :
    x / 2 ≤ x + M * (lam * (v - x) + eta * (x - r)) ∧
    x + M * (lam * (v - x) + eta * (x - r)) ≤ M * v := by
  have hM0 : 0 ≤ M := by linarith
  have hMeta : 0 ≤ M * eta := mul_nonneg hM0 heta
  let c : ℝ := 1 - M * lam + M * eta
  have hc : 1 / 2 ≤ c := by dsimp [c]; linarith
  have hc0 : 0 ≤ c := by linarith
  have hidentity :
      x + M * (lam * (v - x) + eta * (x - r)) =
        c * x + M * lam * v - M * eta * r := by
    dsimp [c]
    ring
  rw [hidentity]
  constructor
  · have hcx := mul_le_mul_of_nonneg_right hc hx
    have hrr := mul_le_mul_of_nonneg_left hrM hMeta
    have hremaining : 0 ≤ M * ((lam - M * eta) * v) :=
      mul_nonneg hM0 (mul_nonneg (sub_nonneg.mpr hetaM) hv)
    nlinarith only [hcx, hrr, hremaining]
  · have hcx := mul_le_mul_of_nonneg_left hxM hc0
    have hdrop : 0 ≤ M * eta * r := mul_nonneg hMeta hr
    have hbracket : (1 - M) * lam + M * eta ≤ 0 := by
      have haux : 0 ≤ (M - 2) * lam :=
        mul_nonneg (sub_nonneg.mpr hM) hlam
      nlinarith only [haux, hetaM]
    have hcorrection :
        (M * v) * ((1 - M) * lam + M * eta) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hM0 hv) hbracket
    calc
      c * x + M * lam * v - M * eta * r ≤ c * (M * v) + M * lam * v := by
        linarith only [hcx, hdrop]
      _ = M * v + (M * v) * ((1 - M) * lam + M * eta) := by
        dsimp [c]
        ring
      _ ≤ M * v := by linarith only [hcorrection]

/-- A trapped coordinate cannot block an elimination augmentation of size at
most M: if it starts positive it stays at least half as large, and it remains
below M times its target value. -/
theorem elimination_conformal_coordinate_bounds
    (M v x r lam eta g alpha : ℝ)
    (hM : 2 ≤ M) (hv : 0 ≤ v) (hx : 0 ≤ x) (hr : 0 ≤ r)
    (hxM : x ≤ M * v) (hrM : r ≤ M * v)
    (hlam : 0 ≤ lam) (heta : 0 ≤ eta)
    (hlamM : M * lam ≤ 1 / 2) (hetaM : M * eta ≤ lam)
    (hpiece : ScalarConformalPiece g (lam * (v - x) + eta * (x - r)))
    (halpha : 0 ≤ alpha) (halphaM : alpha ≤ M) :
    x / 2 ≤ x + alpha * g ∧ x + alpha * g ≤ M * v := by
  obtain ⟨hlower, hupper⟩ := elimination_full_displacement_bounds
    M v x r lam eta hM hv hx hr hxM hrM hlam heta hlamM hetaM
  have hM0 : 0 ≤ M := by linarith
  rcases hpiece with ⟨hg0, hgd⟩ | ⟨hdg, hg0⟩
  · have hstep0 : 0 ≤ alpha * g := mul_nonneg halpha hg0
    have hstepM := mul_le_mul_of_nonneg_right halphaM hg0
    have hMg := mul_le_mul_of_nonneg_left hgd hM0
    constructor <;> linarith
  · have hstep0 : alpha * g ≤ 0 := mul_nonpos_of_nonneg_of_nonpos halpha hg0
    have hstepM := mul_le_mul_of_nonpos_right halphaM hg0
    have hMg := mul_le_mul_of_nonneg_left hdg hM0
    constructor <;> linarith

/-- The auxiliary extrapolation coefficient is bounded by rho whenever
0 ≤ rho ≤ lambda ≤ 1 and rho < 1. -/
theorem extrapolation_eta_bounds
    (lam rho : ℝ) (hlam : lam ≤ 1) (hrho : 0 ≤ rho)
    (hrholam : rho ≤ lam) (hrho1 : rho < 1) :
    0 ≤ (1 - lam) * rho / (1 - rho) ∧
    (1 - lam) * rho / (1 - rho) ≤ rho := by
  have hden : 0 < 1 - rho := sub_pos.mpr hrho1
  constructor
  · exact div_nonneg (mul_nonneg (sub_nonneg.mpr hlam) hrho) (le_of_lt hden)
  · apply (div_le_iff₀ hden).2
    have hmul := mul_le_mul_of_nonneg_right hrholam hrho
    nlinarith only [hmul]

/-- The simpler norm-reduction step also preserves the trapped upper bound. -/
theorem norm_step_trapped_upper
    (M v x g alpha : ℝ)
    (hM : 1 ≤ M) (hx : 0 ≤ x) (hxM : x ≤ M * v)
    (hpiece : ScalarConformalPiece g (v - x))
    (halpha : 0 ≤ alpha) (halphaM : alpha ≤ M) :
    x + alpha * g ≤ M * v := by
  have hM0 : 0 ≤ M := by linarith
  rcases hpiece with ⟨hg0, hgd⟩ | ⟨_, hg0⟩
  · have ha := mul_le_mul_of_nonneg_right halphaM hg0
    have hg := mul_le_mul_of_nonneg_left hgd hM0
    have hnonneg : 0 ≤ (M - 1) * x := mul_nonneg (sub_nonneg.mpr hM) hx
    nlinarith only [ha, hg, hnonneg]
  · have ha := mul_nonpos_of_nonneg_of_nonpos halpha hg0
    linarith

/-- Integer envelope for n event phases and at most 4 M^2+1 steps per phase. -/
theorem event_budget_le_cubic
    (n M : ℕ) (hn : 1 ≤ n) (hM : M ≤ 2 * n) :
    n * (4 * M ^ 2 + 1) ≤ 17 * n ^ 3 := by
  have hsq := Nat.mul_le_mul hM hM
  have hnsq := Nat.mul_le_mul hn hn
  have hstage : 4 * M ^ 2 + 1 ≤ 17 * n ^ 2 := by
    nlinarith only [hsq, hnsq]
  calc
    n * (4 * M ^ 2 + 1) ≤ n * (17 * n ^ 2) := Nat.mul_le_mul_left n hstage
    _ = 17 * n ^ 3 := by ring

#print axioms scalarConformalPiece_of_sign_abs
#print axioms elimination_full_displacement_bounds
#print axioms elimination_conformal_coordinate_bounds
#print axioms extrapolation_eta_bounds
#print axioms norm_step_trapped_upper
#print axioms event_budget_le_cubic

end HirschCircuit
