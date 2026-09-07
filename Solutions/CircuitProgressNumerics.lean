import Mathlib

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCircuitProgress

/-- A summand in a conformal decomposition has the same coordinate signs
as the total displacement and does not exceed its coordinate magnitudes. -/
def ConformalPart {ι : Type*} (g delta : ι → ℝ) : Prop :=
  ∀ i, min 0 (delta i) ≤ g i ∧ g i ≤ max 0 (delta i)

lemma conformal_bounds {ι : Type*} {g delta : ι → ℝ}
    (h : ConformalPart g delta) (i : ι) :
    (0 ≤ delta i → 0 ≤ g i ∧ g i ≤ delta i) ∧
    (delta i ≤ 0 → delta i ≤ g i ∧ g i ≤ 0) := by
  constructor
  · intro hi
    simpa only [min_eq_left hi, max_eq_right hi] using h i
  · intro hi
    simpa only [min_eq_right hi, max_eq_left hi] using h i

/-- A conformal unit step toward a nonnegative target remains nonnegative. -/
lemma conformal_unit_feasible {ι : Type*} (x v g : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hv : ∀ i, 0 ≤ v i)
    (hg : ConformalPart g (fun i => v i - x i)) :
    ∀ i, 0 ≤ x i + g i := by
  intro i
  by_cases h : x i ≤ v i
  · have hb := (conformal_bounds hg i).1 (sub_nonneg.mpr h)
    linarith [hx i]
  · have hb := (conformal_bounds hg i).2 (sub_nonpos.mpr (le_of_not_ge h))
    linarith [hv i]

/-- The selected circuit's weighted gain controls both the maximal scalar
and the trapped invariant. Cross-multiplied contraction avoids division. -/
theorem greedy_norm_step
    {ι : Type*} [Fintype ι] (N : Finset ι)
    (x v g weight : ι → ℝ) (M alpha : ℝ)
    (hM : 1 ≤ M) (ha : 1 ≤ alpha)
    (hx : ∀ i, 0 ≤ x i) (hv : ∀ i, 0 ≤ v i)
    (hweight : ∀ i ∈ N, 0 ≤ weight i)
    (hvN : ∀ i ∈ N, v i = 0)
    (hconf : ConformalPart g (fun i => v i - x i))
    (hfeas : ∀ i, 0 ≤ x i + alpha * g i)
    (hmass : 0 < ∑ i ∈ N, weight i * x i)
    (hgain : (∑ i ∈ N, weight i * x i) ≤
      M * (∑ i ∈ N, weight i * (-g i))) :
    alpha ≤ M ∧
    M * (∑ i ∈ N, weight i * (x i + alpha * g i)) ≤
      (M - 1) * (∑ i ∈ N, weight i * x i) ∧
    (∀ i, x i ≤ M * v i → x i + alpha * g i ≤ M * v i) ∧
    (∀ i ∈ N, x i + alpha * g i ≤ x i) := by
  have hMpos : 0 < M := by linarith
  have hapos : 0 < alpha := by linarith
  have hgN : ∀ i ∈ N, g i ≤ 0 := by
    intro i hi
    have hb := (conformal_bounds hconf i).2
      (by rw [hvN i hi]; linarith [hx i])
    exact hb.2
  let S := ∑ i ∈ N, weight i * x i
  let G := ∑ i ∈ N, weight i * (-g i)
  let S' := ∑ i ∈ N, weight i * (x i + alpha * g i)
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun i hi =>
    mul_nonneg (hweight i hi) (neg_nonneg.mpr (hgN i hi))
  have hS'0 : 0 ≤ S' := Finset.sum_nonneg fun i hi =>
    mul_nonneg (hweight i hi) (hfeas i)
  have hrel : S' = S - alpha * G := by
    dsimp [S', S, G]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hSpos : 0 < S := hmass
  have hSG : S ≤ M * G := hgain
  have hGpos : 0 < G := by nlinarith
  have halpha : alpha ≤ M := by nlinarith [hrel]
  have hcontract : M * S' ≤ (M - 1) * S := by
    have hαG : G ≤ alpha * G := by nlinarith
    have hS' : S' ≤ S - G := by linarith [hrel]
    have hmul := mul_le_mul_of_nonneg_left hS' hMpos.le
    nlinarith
  refine ⟨halpha, hcontract, ?_, ?_⟩
  · intro i htrap
    by_cases hi : x i ≤ v i
    · have hb := (conformal_bounds hconf i).1 (sub_nonneg.mpr hi)
      have hprod : alpha * g i ≤ M * (v i - x i) :=
        mul_le_mul halpha hb.2 hb.1 hMpos.le
      have hMx : x i ≤ M * x i := by nlinarith [hx i]
      linarith
    · have hb := (conformal_bounds hconf i).2 (sub_nonpos.mpr (le_of_not_ge hi))
      have hnonpos := mul_nonpos_of_nonneg_of_nonpos hapos.le hb.2
      linarith
  · intro i hi
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos hapos.le (hgN i hi)
    linarith

/-- Scalar protection estimate for an elimination step. Both the current and
reference coordinate are trapped. `eta` is the extrapolation coefficient;
`lambda` is the pull toward the target. Positive trapped coordinates stay
strictly positive, so none can be the limiting coordinate of a maximal step. -/
theorem elimination_trapped_coordinate
    (M alpha lambda eta x ref v g : ℝ)
    (hM : 2 ≤ M) (ha0 : 0 ≤ alpha) (haM : alpha ≤ M)
    (hl : 0 ≤ lambda) (he : 0 ≤ eta)
    (hprotect : eta * M ≤ lambda / 2)
    (hsmall : (lambda + eta) * M ^ 2 ≤ 5 / 16)
    (hx0 : 0 ≤ x) (hr0 : 0 ≤ ref) (hv0 : 0 ≤ v)
    (hxM : x ≤ M * v) (hrM : ref ≤ M * v)
    (hconf : min 0 (lambda * (v - x) + eta * (x - ref)) ≤ g ∧
      g ≤ max 0 (lambda * (v - x) + eta * (x - ref))) :
    x + alpha * g ≤ M * v ∧ (0 < x → 0 < x + alpha * g) := by
  let delta := lambda * (v - x) + eta * (x - ref)
  have hM0 : 0 ≤ M := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hMv : v ≤ M * v := by nlinarith
  have hdhi : delta ≤ (lambda + eta) * M * v := by
    have h1 := mul_le_mul_of_nonneg_left (show v - x ≤ M * v by linarith) hl
    have h2 := mul_le_mul_of_nonneg_left (show x - ref ≤ M * v by linarith) he
    dsimp [delta]
    nlinarith
  have hdlo : -(lambda + eta) * M * v ≤ delta := by
    have h1 := mul_le_mul_of_nonneg_left (show -(M * v) ≤ v - x by linarith) hl
    have h2 := mul_le_mul_of_nonneg_left (show -(M * v) ≤ x - ref by linarith) he
    dsimp [delta]
    nlinarith
  have hA0 : 0 ≤ (lambda + eta) * M * v := by positivity
  have hglo : -(lambda + eta) * M * v ≤ g := by
    have hmin : -(lambda + eta) * M * v ≤ min 0 delta :=
      le_min (by nlinarith) hdlo
    exact hmin.trans hconf.1
  have hghi : g ≤ (lambda + eta) * M * v := by
    have hmax : max 0 delta ≤ (lambda + eta) * M * v := max_le hA0 hdhi
    exact hconf.2.trans hmax
  have hsize : (lambda + eta) * M ^ 2 * v ≤ (5 / 16) * v :=
    mul_le_mul_of_nonneg_right hsmall hv0
  have hmovehi : alpha * g ≤ (5 / 16) * v := by
    have h1 := mul_le_mul_of_nonneg_left hghi ha0
    have h2 := mul_le_mul_of_nonneg_right haM hA0
    nlinarith
  have hmovelo : -(5 / 16) * v ≤ alpha * g := by
    have h1 := mul_le_mul_of_nonneg_left hglo ha0
    have h2 := mul_le_mul_of_nonneg_right haM hA0
    nlinarith
  have hdsmall : x ≤ v / 2 → 0 ≤ delta := by
    intro hxs
    have h1 := mul_le_mul_of_nonneg_left (show v / 2 ≤ v - x by linarith) hl
    have h2 := mul_le_mul_of_nonneg_left (show -(M * v) ≤ x - ref by linarith) he
    have h3 := mul_le_mul_of_nonneg_right hprotect hv0
    dsimp [delta]
    nlinarith
  have hdlarge : 3 * v / 2 ≤ x → delta ≤ 0 := by
    intro hxl
    have h1 := mul_le_mul_of_nonneg_left (show v - x ≤ -v / 2 by linarith) hl
    have h2 := mul_le_mul_of_nonneg_left (show x - ref ≤ M * v by linarith) he
    have h3 := mul_le_mul_of_nonneg_right hprotect hv0
    dsimp [delta]
    nlinarith
  constructor
  · by_cases hxl : 3 * v / 2 ≤ x
    · have hd := hdlarge hxl
      have hg : g ≤ 0 := by simpa only [max_eq_left hd] using hconf.2
      have hprod := mul_nonpos_of_nonneg_of_nonpos ha0 hg
      linarith
    · have htwo : 2 * v ≤ M * v := mul_le_mul_of_nonneg_right hM hv0
      linarith
  · intro hxpos
    by_cases hxs : x ≤ v / 2
    · have hd := hdsmall hxs
      have hg : 0 ≤ g := by simpa only [min_eq_left hd] using hconf.1
      have hprod := mul_nonneg ha0 hg
      linarith
    · have hvpos : 0 < v := by
        by_contra h
        have hvz : v = 0 := by linarith
        rw [hvz, mul_zero] at hxM
        linarith
      linarith

#print axioms greedy_norm_step
#print axioms elimination_trapped_coordinate

end HirschCircuitProgress
