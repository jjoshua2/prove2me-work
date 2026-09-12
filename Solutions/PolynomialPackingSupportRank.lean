import Solutions.PolynomialOrthantPackingNormalization

/-!
# Positive support of an orthant-model vertex is bounded by upper-row rank

New uncompiled proof candidate. A direction supported on positive coordinates
and annihilated by every upper row gives a two-sided feasible perturbation.
This proves injectivity on the support, with no assumption about simple
vertices, cube combinatorics, nonnegative upper rows, or a diameter bound.
Nonnegative upper rows are used later to keep the origin in each support face.
-/
open scoped BigOperators
open Set HirschPacking
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace HirschPacking

variable {d m : ℕ}

def upperRowMap (R : Fin m → Fin d → ℝ) : (Fin d → ℝ) →ₗ[ℝ] (Fin m → ℝ) where
  toFun x i := lin (R i) x
  map_add' x y := by ext i; exact map_add (lin (R i)) x y
  map_smul' r x := by ext i; exact map_smul (lin (R i)) r x

/-- Extension by zero from a selected coordinate support. -/
def supportEmbed (S : Finset (Fin d)) : (S → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun z j := if hj : j ∈ S then z ⟨j, hj⟩ else 0
  map_add' x y := by
    ext j
    by_cases hj : j ∈ S <;> simp [hj]
  map_smul' r x := by
    ext j
    by_cases hj : j ∈ S <;> simp [hj]

lemma supportEmbed_injective (S : Finset (Fin d)) : Function.Injective (supportEmbed S) := by
  intro y z h
  funext j
  have hj := congrFun h j.val
  simpa [supportEmbed, j.property] using hj

/-- Positive-support directions are detected by the upper rows at a vertex. -/
theorem upper_eval_injective_on_positive_support
    (R : Fin m → Fin d → ℝ) (x : Fin d → ℝ)
    (hx : x ∈ extremePoints ℝ (orthantModel R))
    (S : Finset (Fin d)) (hS : ∀ j ∈ S, 0 < x j) :
    Function.Injective ((upperRowMap R).comp (supportEmbed S)) := by
  classical
  intro y z hyz
  let v := supportEmbed S (y - z)
  have hRv : upperRowMap R v = 0 := by
    change upperRowMap R (supportEmbed S (y - z)) = 0
    rw [map_sub, map_sub]
    change (upperRowMap R).comp (supportEmbed S) y -
      (upperRowMap R).comp (supportEmbed S) z = 0
    rw [hyz, sub_self]
  have horth : ∀ i, lin (R i) v = 0 := by
    intro i
    exact congrFun hRv i
  have hlocal : ∀ j : Fin d, ∃ t : ℝ, 0 < t ∧ t * |v j| ≤ x j := by
    intro j
    by_cases hj : j ∈ S
    · have hxj := hS j hj
      refine ⟨x j / (|v j| + 1), div_pos hxj (by positivity), ?_⟩
      have hden : 0 < |v j| + 1 := by positivity
      have heq := div_mul_cancel₀ (x j) (ne_of_gt hden)
      have hnonneg : 0 ≤ x j / (|v j| + 1) := (div_pos hxj hden).le
      nlinarith
    · refine ⟨1, zero_lt_one, ?_⟩
      have hvj : v j = 0 := by simp [v, supportEmbed, hj]
      simpa [hvj] using hx.1.1 j
  choose e hepos hebound using hlocal
  have huniform : ∀ F : Finset (Fin d), ∃ t : ℝ,
      0 < t ∧ ∀ j ∈ F, t ≤ e j := by
    intro F
    induction F using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert j F hj ih =>
      obtain ⟨t, ht, hle⟩ := ih
      refine ⟨min (e j) t, lt_min (hepos j) ht, ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with hkj | hkF
      · subst k
        exact min_le_left _ _
      · exact (min_le_right _ _).trans (hle k hkF)
  obtain ⟨t, ht, hte⟩ := huniform Finset.univ
  have hbound : ∀ j, t * |v j| ≤ x j := by
    intro j
    exact (mul_le_mul_of_nonneg_right (hte j (Finset.mem_univ j))
      (abs_nonneg _)).trans (hebound j)
  have hp : x + t • v ∈ orthantModel R := by
    constructor
    · intro j
      change 0 ≤ x j + t * v j
      have h := mul_le_mul_of_nonneg_left (neg_le_abs (v j)) ht.le
      rw [mul_neg] at h
      linarith [hbound j]
    · intro i
      simpa [map_add, map_smul, horth] using hx.1.2 i
  have hm : x - t • v ∈ orthantModel R := by
    constructor
    · intro j
      change 0 ≤ x j - t * v j
      have h := mul_le_mul_of_nonneg_left (le_abs_self (v j)) ht.le
      linarith [hbound j]
    · intro i
      simpa [map_sub, map_smul, horth] using hx.1.2 i
  have hmid : x ∈ openSegment ℝ (x + t • v) (x - t • v) := by
    refine ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
    module
  have heq := hx.2 hp hm hmid
  have htv : t • v = 0 := by
    have h := congrArg (fun a => a - x) heq
    simpa using h
  have hv : v = 0 := (smul_eq_zero.mp htv).resolve_left (ne_of_gt ht)
  apply supportEmbed_injective S
  apply sub_eq_zero.mp
  simpa only [v, map_sub] using hv

/-- Cardinality bound through the rank of the whole upper-row evaluation. -/
theorem positive_support_card_le_upper_rank
    (R : Fin m → Fin d → ℝ) (x : Fin d → ℝ)
    (hx : x ∈ extremePoints ℝ (orthantModel R))
    (S : Finset (Fin d)) (hS : ∀ j ∈ S, 0 < x j) :
    S.card ≤ Module.finrank ℝ (upperRowMap R).range := by
  let T : (S → ℝ) →ₗ[ℝ] (upperRowMap R).range :=
    (upperRowMap R).rangeRestrict.comp (supportEmbed S)
  have hinj : Function.Injective T := by
    intro y z h
    apply upper_eval_injective_on_positive_support R x hx S hS
    exact congrArg Subtype.val h
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Fintype.card_coe] using hdim

#print axioms upper_eval_injective_on_positive_support
#print axioms positive_support_card_le_upper_rank
end HirschPacking
