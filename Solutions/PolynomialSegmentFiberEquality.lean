import Mathlib

/-!
# Exact segment summands directly from finite halfspaces

The pairwise condition below proves equality with the endpoint erosion plus a
segment, not merely nonempty erosion or an inclusion. A minimum positive-row
ratio supplies the decomposition parameter for every point. No diameter input,
vertex enumeration, convexity oracle, or proposed coarse polytope is assumed.

NEW UNCOMPILED proof candidates. Finite LP discovery is separate executable
work. Its Farkas and sharpness witnesses are interpreted in the companion file.
-/
open Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace HirschSegmentPeeling
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {ι : Type*} [Fintype ι]

/-- An arbitrary finite original halfspace description, including redundancies. -/
def halfspaces (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) : Set E :=
  {x | ∀ i, a i x ≤ b i}

/-- The exact set of points whose segment endpoints both satisfy the H-system. -/
def erosion (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g : E) (τ : ℝ) : Set E :=
  halfspaces a (fun i => b i-τ*max (a i g) 0)

/-- Parameterized Minkowski addition. This definition also permits point cores. -/
def segmentSum (P : Set E) (g : E) (τ : ℝ) : Set E :=
  {x | ∃ p ∈ P, ∃ t : ℝ, 0 ≤ t ∧ t ≤ τ ∧ x=p+t • g}

lemma segment_scalar_bound (α t τ : ℝ) (ht : 0 ≤ t) (htτ : t ≤ τ) :
    t*α ≤ τ*max α 0 := by
  by_cases hα : 0 ≤ α
  · rw [max_eq_left hα]
    exact mul_le_mul_of_nonneg_right htτ hα
  · have hα' : α ≤ 0 := le_of_not_ge hα
    rw [max_eq_right hα']
    nlinarith

/-- The erosion always gives this inclusion. Equality needs the pair test. -/
theorem eroded_segment_subset
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g : E) (τ : ℝ) :
    segmentSum (erosion a b g τ) g τ ⊆ halfspaces a b := by
  rintro x ⟨p,hp,t,ht,htτ,rfl⟩ i
  have h := hp i
  have hs := segment_scalar_bound (a i g) t τ ht htτ
  simp only [map_add,map_smul,smul_eq_mul]
  linarith

lemma split_parameter_bounds (τ U : ℝ) (hτ : 0 ≤ τ) (hU : 0 ≤ U) :
    0 ≤ max 0 (τ-U) ∧ max 0 (τ-U) ≤ τ ∧ τ-max 0 (τ-U) ≤ U := by
  refine ⟨le_max_left _ _, max_le hτ (by linarith), ?_⟩
  have h := le_max_right 0 (τ-U)
  linarith

/-- A concrete minimum among the positive row ratios; no minimum is assumed. -/
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
    obtain ⟨i,hi⟩ := hplus
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩
  obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image S (fun j => (b j-a j x)/(a j g)) hS
  have hip : 0 < a i g := (Finset.mem_filter.mp hi).2
  refine ⟨i,hip,div_nonneg (sub_nonneg.mpr (hx i)) hip.le,?_⟩
  intro j hj
  have h := hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ j,hj⟩)
  exact (le_div_iff₀ hj).mp h

/-- All opposing-row fiber widths at least τ imply the WHOLE Minkowski equality.
Only a finite positive-row minimum is needed. A lower row may be absent; the
condition then remains a valid sufficient statement for an unbounded set. -/
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
    obtain ⟨i,hip,hU,hupper⟩ := exists_upper_fiber_end a b g x hx hplus
    let U := (b i-a i x)/(a i g)
    let t := max 0 (τ-U)
    have hU0 : 0 ≤ U := hU
    obtain ⟨ht0,htτ,htU⟩ := split_parameter_bounds τ U hτ hU0
    have hUi : U*(a i g)=b i-a i x := div_mul_cancel₀ _ (ne_of_gt hip)
    refine ⟨x-t • g,?_,t,ht0,htτ,?_⟩
    · intro j
      have hj := hx j
      simp only [map_sub,map_smul,smul_eq_mul]
      by_cases hjpos : 0 < a j g
      · rw [max_eq_left hjpos.le]
        have hbound := hupper j hjpos
        have hmul := mul_le_mul_of_nonneg_right htU hjpos.le
        dsimp [t,U] at *
        nlinarith
      · have hjnon : a j g ≤ 0 := le_of_not_gt hjpos
        rw [max_eq_right hjnon]
        by_cases hjzero : a j g=0
        · simp [hjzero]
          exact hj
        · have hjneg : a j g < 0 := lt_of_le_of_ne hjnon hjzero
          have pair := hpairs x hx i j hip hjneg
          have pair' : τ*(a i g)*(-a j g) ≤
              (-a j g)*(U*(a i g))+(a i g)*(b j-a j x) := by
            rw [hUi]
            exact pair
          have hbound : (τ-U)*(-a j g) ≤ b j-a j x := by
            nlinarith [pair']
          by_cases hdiff : τ-U ≤ 0
          · have ht : t=0 := max_eq_left hdiff
            simp only [ht,zero_mul,mul_zero,sub_zero]
            exact hj
          · have ht : t=τ-U := max_eq_right (le_of_not_ge hdiff)
            rw [ht]
            nlinarith
    · module
  · exact eroded_segment_subset a b g τ

#print axioms segment_scalar_bound
#print axioms eroded_segment_subset
#print axioms exists_upper_fiber_end
#print axioms segment_equality_of_pair_widths
end HirschSegmentPeeling
