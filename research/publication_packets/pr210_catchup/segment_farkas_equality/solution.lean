import Mathlib

open Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace HirschSegmentPeelingPublic

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {ι : Type*} [Fintype ι]

def halfspaces (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) : Set E :=
  {x | ∀ i, a i x ≤ b i}

def erosion (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g : E) (τ : ℝ) : Set E :=
  halfspaces a (fun i => b i - τ * max (a i g) 0)

def segmentSum (P : Set E) (g : E) (τ : ℝ) : Set E :=
  {x | ∃ p ∈ P, ∃ t : ℝ, 0 ≤ t ∧ t ≤ τ ∧ x = p + t • g}

lemma segment_scalar_bound (α t τ : ℝ) (ht : 0 ≤ t) (htτ : t ≤ τ) :
    t * α ≤ τ * max α 0 := by
  by_cases hα : 0 ≤ α
  · rw [max_eq_left hα]
    exact mul_le_mul_of_nonneg_right htτ hα
  · have hα' : α ≤ 0 := le_of_not_ge hα
    rw [max_eq_right hα']
    nlinarith

theorem eroded_segment_subset
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g : E) (τ : ℝ) :
    segmentSum (erosion a b g τ) g τ ⊆ halfspaces a b := by
  rintro x ⟨p, hp, t, ht, htτ, rfl⟩ i
  have h := hp i
  have hs := segment_scalar_bound (a i g) t τ ht htτ
  simp only [map_add, map_smul, smul_eq_mul]
  linarith

lemma split_parameter_bounds (τ U : ℝ) (hτ : 0 ≤ τ) (hU : 0 ≤ U) :
    0 ≤ max 0 (τ-U) ∧ max 0 (τ-U) ≤ τ ∧ τ-max 0 (τ-U) ≤ U := by
  refine ⟨le_max_left _ _, max_le hτ (by linarith), ?_⟩
  have h := le_max_right 0 (τ-U)
  linarith

theorem exists_upper_fiber_end
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g x : E)
    (hx : x ∈ halfspaces a b) (hplus : ∃ i, 0 < a i g) :
    ∃ i : ι, 0 < a i g ∧
      0 ≤ (b i-a i x)/(a i g) ∧
      ∀ j, 0 < a j g →
        ((b i-a i x)/(a i g))*(a j g) ≤ b j-a j x := by
  classical
  let S := Finset.univ.filter (fun i : ι => 0 < a i g)
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := hplus
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image S (fun j => (b j-a j x)/(a j g)) hS
  have hip : 0 < a i g := (Finset.mem_filter.mp hi).2
  refine ⟨i, hip, div_nonneg (sub_nonneg.mpr (hx i)) hip.le, ?_⟩
  intro j hj
  have h := hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
  exact (le_div_iff₀ hj).mp h

theorem segment_equality_of_pair_widths
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g : E) (τ : ℝ)
    (hτ : 0 ≤ τ) (hplus : ∃ i, 0 < a i g)
    (hpairs : ∀ x ∈ halfspaces a b, ∀ i j,
      0 < a i g → a j g < 0 →
      τ*(a i g)*(-a j g) ≤
        (-a j g)*(b i-a i x)+(a i g)*(b j-a j x)) :
    halfspaces a b = segmentSum (erosion a b g τ) g τ := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i, hip, hU, hupper⟩ := exists_upper_fiber_end a b g x hx hplus
    let U := (b i-a i x)/(a i g)
    let t := max 0 (τ-U)
    have hU0 : 0 ≤ U := hU
    obtain ⟨ht0, htτ, htU⟩ := split_parameter_bounds τ U hτ hU0
    have hUi : U*(a i g)=b i-a i x := div_mul_cancel₀ _ (ne_of_gt hip)
    refine ⟨x-t • g, ?_, t, ht0, htτ, ?_⟩
    · intro j
      have hj := hx j
      simp only [map_sub, map_smul, smul_eq_mul]
      by_cases hjpos : 0 < a j g
      · rw [max_eq_left hjpos.le]
        have hbound := hupper j hjpos
        have hmul := mul_le_mul_of_nonneg_right htU hjpos.le
        dsimp [t, U] at *
        nlinarith
      · have hjnon : a j g ≤ 0 := le_of_not_gt hjpos
        rw [max_eq_right hjnon]
        by_cases hjzero : a j g = 0
        · simp [hjzero]
          exact hj
        · have hjneg : a j g < 0 := lt_of_le_of_ne hjnon hjzero
          have pair := hpairs x hx i j hip hjneg
          have pair' : τ*(a i g)*(-a j g) ≤
              (-a j g)*(U*(a i g))+(a i g)*(b j-a j x) := by
            rw [hUi]
            exact pair
          have hbound : (τ-U)*(-a j g) ≤ b j-a j x := by
            apply (mul_le_mul_left hip).mp
            nlinarith [pair']
          by_cases hdiff : τ-U ≤ 0
          · have ht : t = 0 := max_eq_left hdiff
            simp only [ht, zero_mul, mul_zero, sub_zero]
            exact hj
          · have ht : t = τ-U := max_eq_right (le_of_not_ge hdiff)
            rw [ht]
            nlinarith
    · module
  · exact eroded_segment_subset a b g τ

structure PairCertificate
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g : E) (τ : ℝ) (i j : ι) where
  weights : ι → ℝ
  nonnegative : ∀ k, 0 ≤ weights k
  normal_identity : ∑ k, weights k • a k = (-a j g) • a i + (a i g) • a j
  constant_bound : (∑ k, weights k*b k) ≤
    (-a j g)*b i + (a i g)*b j - τ*(a i g)*(-a j g)

theorem PairCertificate.pointwise
    {a : ι → E →ₗ[ℝ] ℝ} {b : ι → ℝ} {g : E} {τ : ℝ} {i j : ι}
    (c : PairCertificate a b g τ i j)
    (x : E) (hx : x ∈ halfspaces a b) :
    τ*(a i g)*(-a j g) ≤ (-a j g)*(b i-a i x)+(a i g)*(b j-a j x) := by
  have hs : (∑ k, c.weights k*a k x) ≤ ∑ k, c.weights k*b k := by
    exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hx k) (c.nonnegative k))
  have he := congrArg (fun f : E →ₗ[ℝ] ℝ => f x) c.normal_identity
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul] at he
  have hb := c.constant_bound
  nlinarith

theorem segment_equality_of_farkas
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g : E) (τ : ℝ)
    (hτ : 0 ≤ τ) (hplus : ∃ i, 0 < a i g)
    (cert : ∀ i j, 0 < a i g → a j g < 0 → PairCertificate a b g τ i j) :
    halfspaces a b = segmentSum (erosion a b g τ) g τ := by
  apply segment_equality_of_pair_widths a b g τ hτ hplus
  intro x hx i j hi hj
  exact (cert i j hi hj).pointwise x hx

end HirschSegmentPeelingPublic
end

theorem solution
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι]
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g : E) (τ : ℝ)
    (hτ : 0 ≤ τ) (hplus : ∃ i, 0 < a i g)
    (cert : ∀ i j, 0 < a i g → a j g < 0 →
      HirschSegmentPeelingPublic.PairCertificate a b g τ i j) :
    HirschSegmentPeelingPublic.halfspaces a b =
      HirschSegmentPeelingPublic.segmentSum
        (HirschSegmentPeelingPublic.erosion a b g τ) g τ := by
  exact HirschSegmentPeelingPublic.segment_equality_of_farkas a b g τ hτ hplus cert

#print axioms solution
