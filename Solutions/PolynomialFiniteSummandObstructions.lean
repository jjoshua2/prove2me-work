import Mathlib

/-!
# Finite candidate hulls: support deficits and sharp summand obstructions

The companion exact algorithm enumerates positive circuits of an allocation
system, then verifies original-row Farkas witnesses. This file supplies finite
weighted-support and allocation-obstruction cores. It does NOT import the full
Farkas alternative or pretend that circuit enumeration has already been proved
complete in Lean. The complete geometric argument is in the paper handoff.
NEW UNCOMPILED candidates; no platform verdict is asserted.
-/
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HirschFiniteSummand
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Convex hull of zero and the listed vectors, scaled by a nonnegative budget.
Affine dependence of the list does not invalidate this representation. -/
def scaledHull (G : κ → E) (τ : ℝ) : Set E :=
  {q | ∃ θ : κ → ℝ, (∀ j, 0 ≤ θ j) ∧ (∑ j, θ j) ≤ τ ∧
    q = ∑ j, θ j • G j}

theorem scaledHull_support_bound
    (G : κ → E) (f : E →ₗ[ℝ] ℝ) (h τ : ℝ)
    (hh : 0 ≤ h) (hG : ∀ j, f (G j) ≤ h)
    {q : E} (hq : q ∈ scaledHull G τ) : f q ≤ τ*h := by
  obtain ⟨θ,hθ,ht,rfl⟩ := hq
  rw [map_sum]
  simp only [map_smul,smul_eq_mul]
  calc
    (∑ j, θ j * f (G j)) ≤ ∑ j, θ j*h :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hG j) (hθ j))
    _ = (∑ j, θ j)*h := by rw [Finset.sum_mul]
    _ ≤ τ*h := mul_le_mul_of_nonneg_right ht hh

/-- Positive combinations of original inequalities certify a global bound.
The implementation stores the coefficients sparsely but checks this identity. -/
theorem original_row_combination_bound
    (a : ι → E →ₗ[ℝ] ℝ) (b weight : ι → ℝ) (x : E)
    (hweight : ∀ i, 0 ≤ weight i) (hx : ∀ i, a i x ≤ b i) :
    (∑ i, weight i • a i) x ≤ ∑ i, weight i*b i := by
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hx i) (hweight i))

/-- A candidate support bound on the combined normal controls its allocation. -/
theorem allocation_weighted_bound
    (a : ι → E →ₗ[ℝ] ℝ) (G : κ → E) (weight : ι → ℝ)
    (ν τ : ℝ) (hν : 0 ≤ ν)
    (hG : ∀ j, (∑ i, weight i * a i (G j)) ≤ ν)
    {q : E} (hq : q ∈ scaledHull G τ) :
    (∑ i, weight i • a i) q ≤ τ*ν := by
  apply scaledHull_support_bound G (∑ i, weight i • a i) ν τ hν _ hq
  intro j
  simpa only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul] using hG j

/-- Every decomposition into the endpoint erosion plus the scaled hull obeys
all support-deficit inequalities. This lemma itself needs no enumeration. -/
theorem decomposition_obeys_support_deficit
    (a : ι → E →ₗ[ℝ] ℝ) (b h weight : ι → ℝ) (G : κ → E)
    (τ ν : ℝ) (x p q : E) (hweight : ∀ i, 0 ≤ weight i)
    (hp : ∀ i, a i p ≤ b i-τ*h i)
    (hν : 0 ≤ ν) (hG : ∀ j, (∑ i, weight i*a i (G j)) ≤ ν)
    (hq : q ∈ scaledHull G τ) (hx : x=p+q) :
    τ*((∑ i, weight i*h i)-ν) ≤
      (∑ i, weight i*b i)-(∑ i, weight i*a i x) := by
  have hbase := original_row_combination_bound a (fun i => b i-τ*h i) weight p hweight hp
  have hadded := allocation_weighted_bound a G weight ν τ hν hG hq
  have he : (∑ i, weight i • a i) x =
      (∑ i, weight i • a i) p+(∑ i, weight i • a i) q := by rw [hx,map_add]
  have hb : (∑ i, weight i*(b i-τ*h i)) =
      (∑ i, weight i*b i)-τ*(∑ i, weight i*h i) := by
    simp only [mul_sub,Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hb] at hbase
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul] at hbase hadded he
  nlinarith

/-- A strict violation is an actual failure to allocate this original point,
not merely a failure of an optimization heuristic. -/
theorem violated_deficit_forbids_allocation
    (a : ι → E →ₗ[ℝ] ℝ) (b h weight : ι → ℝ) (G : κ → E)
    (τ ν : ℝ) (x : E) (hweight : ∀ i, 0 ≤ weight i)
    (hν : 0 ≤ ν) (hG : ∀ j, (∑ i, weight i*a i (G j)) ≤ ν)
    (hbad : (∑ i, weight i*b i)-(∑ i, weight i*a i x) <
      τ*((∑ i, weight i*h i)-ν)) :
    ¬ ∃ p q : E, (∀ i, a i p ≤ b i-τ*h i) ∧
      q ∈ scaledHull G τ ∧ x=p+q := by
  rintro ⟨p,q,hp,hq,hx⟩
  have hcert := decomposition_obeys_support_deficit a b h weight G τ ν x p q
    hweight hp hν hG hq hx
  linarith

/-- A sharp point and a positive support deficit cap every admissible scale. -/
theorem sharp_deficit_caps_scale (s μ gap slack : ℝ)
    (hgap : 0 < gap) (hadmissible : s*gap ≤ slack)
    (hsharp : slack=μ*gap) : s ≤ μ := by
  nlinarith [hadmissible, hsharp, hgap]

/-- Pairwise feasibility is insufficient already for a triangular candidate.
The circuit uses the two lower allocations and the simplex total bound. -/
theorem triangle_triple_obstruction (s x y : ℝ) (hs : 0 < s)
    (hx : s ≤ x) (hy : s ≤ y) : ¬ x+y ≤ s := by linarith

#print axioms scaledHull_support_bound
#print axioms original_row_combination_bound
#print axioms allocation_weighted_bound
#print axioms decomposition_obeys_support_deficit
#print axioms violated_deficit_forbids_allocation
#print axioms sharp_deficit_caps_scale
#print axioms triangle_triple_obstruction
end HirschFiniteSummand
