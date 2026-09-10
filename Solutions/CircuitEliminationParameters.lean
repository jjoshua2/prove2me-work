import Solutions.CircuitEliminationStep

set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace HirschCircuit

/-- Concrete elimination parameters. No maximum-ratio selector is needed:
any positive target-zero coordinate with small enough reference ratio works.
This is a simplification of our support-safe adaptation, not a sharper source
claim. The output is a genuine maximal circuit step with strict progress. -/
theorem exists_elimination_step_of_small_ratio {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (M : ℕ)
    (hM : 2 ≤ M) (hnM : n ≤ M)
    (v r x : Fin n → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (hr : r ∈ StandardSlice K v) (hx : x ∈ StandardSlice K v)
    (heq : phaseProgressSet (M : ℝ) v r = phaseProgressSet (M : ℝ) v x)
    (q : Fin n) (hvq : v q = 0) (hxq : 0 < x q) (hrq : 0 < r q)
    (hsmall : x q / r q ≤ 1 / (2 * (M : ℝ) ^ 2)) :
    ∃ y : Fin n → ℝ,
      StandardCircuitStep K v x y ∧
      phaseProgressSet (M : ℝ) v x ⊂ phaseProgressSet (M : ℝ) v y ∧
      (∀ i, v i = 0 → y i ≤ x i) ∧
      ∀ i, v i ≠ 0 → x i ≤ (M : ℝ) * v i → x i / 2 ≤ y i := by
  have hMr : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMrpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMrpos
  let lam : ℝ := 1 / (2 * (M : ℝ))
  let tau : ℝ := 1 / (2 * (M : ℝ) ^ 2)
  let rho : ℝ := x q / r q
  let eta : ℝ := (1 - lam) * rho / (1 - rho)
  have hlam : 0 ≤ lam := by dsimp [lam]; positivity
  have hlamId : (M : ℝ) * lam = 1 / 2 := by
    dsimp [lam]
    field_simp [hMne] <;> ring
  have hlamLt : lam < 1 := by nlinarith only [hlamId, hlam, hMr]
  have htauLam : tau ≤ lam := by
    dsimp [tau, lam]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [hMr]
  have htauId : (M : ℝ) * tau = lam := by
    dsimp [tau, lam]
    field_simp [hMne] <;> ring
  have hrhoPos : 0 < rho := div_pos hxq hrq
  have hrhoTau : rho ≤ tau := hsmall
  have hrhoLam : rho ≤ lam := hrhoTau.trans htauLam
  have hrhoLt : rho < 1 := hrhoLam.trans_lt hlamLt
  obtain ⟨heta, hetaRho⟩ := extrapolation_eta_bounds lam rho
    (le_of_lt hlamLt) (le_of_lt hrhoPos) hrhoLam hrhoLt
  have hetaM : (M : ℝ) * eta ≤ lam := by
    calc
      (M : ℝ) * eta ≤ (M : ℝ) * tau :=
        mul_le_mul_of_nonneg_left (hetaRho.trans hrhoTau) (le_of_lt hMrpos)
      _ = lam := htauId
  have hetaLam : eta ≤ lam := hetaRho.trans hrhoLam
  have hN : ∀ i, v i = 0 →
      lam * (v i - x i) + eta * (x i - r i) ≤ 0 := by
    intro i hvi
    have h1 : 0 ≤ (lam - eta) * x i :=
      mul_nonneg (sub_nonneg.mpr hetaLam) (hx.2 i)
    have h2 : 0 ≤ eta * r i := mul_nonneg heta (hr.2 i)
    rw [hvi]
    nlinarith only [h1, h2]
  have hrhoEq : rho * r q = x q := div_mul_cancel₀ _ (ne_of_gt hrq)
  have hetaEq : eta * (1 - rho) = (1 - lam) * rho :=
    div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hrhoLt))
  have hbalance : eta * (r q - x q) = (1 - lam) * x q := by
    calc
      eta * (r q - x q) = (eta * (1 - rho)) * r q := by rw [← hrhoEq]; ring
      _ = ((1 - lam) * rho) * r q := by rw [hetaEq]
      _ = (1 - lam) * x q := by rw [mul_assoc, hrhoEq]
  have hq : lam * (v q - x q) + eta * (x q - r q) = -x q := by
    rw [hvq]
    nlinarith only [hbalance]
  exact exists_support_safe_elimination_step K M hM hnM v r x hv hr hx heq
    lam eta hlam heta (le_of_eq hlamId) hetaM hN q hxq hq

#print axioms exists_elimination_step_of_small_ratio
end HirschCircuit
