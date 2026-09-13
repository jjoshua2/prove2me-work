import Mathlib

/-!
# Every source facet can miss every target facet despite a short global route

The spread box Q={0<=x_i<=1, x_j-x_i<=tau}, 0<tau<1, equals a cube plus a
single diagonal segment. Its source 0 and target 1 are simple, but no proper
source-containing face can meet a target facet. The full face-lattice and
zonotope d+1 diameter arguments are in the paper note; this file proves the
scalar and set-level separation and the exact Minkowski membership criterion.
No theorem here asserts an obstruction to all selective carrier repairs.
-/
open Set
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace HirschSeparatedStars
variable {ι : Type*}

def spreadBox (τ : ℝ) : Set (ι → ℝ) :=
  {x | (∀ i,0≤x i) ∧ (∀ i,x i≤1) ∧ ∀ i j,x j-x i≤τ}

theorem target_tight_forces_all_source_slack (τ : ℝ) (hτ : τ<1)
    (x : ι → ℝ) (hx : x∈spreadBox τ) (j : ι) (hj : x j=1) :
    ∀ i,0<x i := by
  intro i
  have h := hx.2.2 i j
  rw [hj] at h
  linarith

theorem source_target_facets_disjoint (τ : ℝ) (hτ : τ<1) (i j : ι) :
    Disjoint {x : ι → ℝ | x∈spreadBox τ ∧ x i=0}
      {x : ι → ℝ | x∈spreadBox τ ∧ x j=1} := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have h := target_tight_forces_all_source_slack τ hτ x hx.1 j hy.2 i
  linarith [hx.2]

/-- Explicit interval form of the Minkowski decomposition; s is the common
translated lower endpoint and each coordinate stays in an interval of length τ. -/
theorem mem_spreadBox_of_diagonal_interval (τ s : ℝ)
    (hs : 0≤s) (hsτ : s≤1-τ) (x : ι → ℝ)
    (hlow : ∀ i,s≤x i) (hhigh : ∀ i,x i≤s+τ) : x∈spreadBox τ := by
  refine ⟨fun i => hs.trans (hlow i),?_,?_⟩
  · intro i
    have h := hhigh i
    linarith
  · intro i j
    have hi := hlow i
    have hj := hhigh j
    linarith

/-- Choose the diagonal coefficient from a largest coordinate. -/
theorem exists_diagonal_interval_of_mem [Fintype ι] [Nonempty ι]
    (τ : ℝ) (hτ0 : 0≤τ) (hτ1 : τ≤1)
    (x : ι → ℝ) (hx : x∈spreadBox τ) :
    ∃ s : ℝ,0≤s ∧ s≤1-τ ∧ (∀ i,s≤x i) ∧ ∀ i,x i≤s+τ := by
  classical
  obtain ⟨j,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset ι) x
    Finset.univ_nonempty
  let s := max 0 (x j-τ)
  refine ⟨s,le_max_left _ _,?_,?_,?_⟩
  · apply max_le
    · linarith
    · have h := hx.2.1 j
      linarith
  · intro i
    apply max_le (hx.1 i)
    have h := hx.2.2 i j
    linarith
  · intro i
    have h₁ : x i≤x j := hmax i (Finset.mem_univ i)
    have h₂ : x j-τ≤s := le_max_right _ _
    linarith

#print axioms target_tight_forces_all_source_slack
#print axioms source_target_facets_disjoint
#print axioms mem_spreadBox_of_diagonal_interval
#print axioms exists_diagonal_interval_of_mem
end HirschSeparatedStars
