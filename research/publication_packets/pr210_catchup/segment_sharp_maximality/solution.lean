import Mathlib

open Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace HirschSegmentSharpPublic

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {ι : Type*} [Fintype ι]

def halfspaces (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) : Set E :=
  {x | ∀ i, a i x ≤ b i}

def segmentSum (P : Set E) (g : E) (τ : ℝ) : Set E :=
  {x | ∃ p ∈ P, ∃ t : ℝ, 0 ≤ t ∧ t ≤ τ ∧ x = p + t • g}

theorem any_segment_summand_le_sharp_width
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g x : E) (τ s : ℝ)
    (i j : ι) (hi : 0 < a i g) (hj : a j g < 0)
    (hx : x ∈ halfspaces a b)
    (hsharp : (-a j g)*(b i-a i x)+(a i g)*(b j-a j x) = τ*(a i g)*(-a j g))
    (P : Set E) (hs : 0 ≤ s) (hdecomp : halfspaces a b = segmentSum P g s) : s ≤ τ := by
  have hx' : x ∈ segmentSum P g s := by rw [←hdecomp]; exact hx
  obtain ⟨p,hp,t,ht0,hts,hxpt⟩ := hx'
  have hp0 : p ∈ halfspaces a b := by
    rw [hdecomp]
    exact ⟨p,hp,0,le_rfl,hs,by simp⟩
  have hp1 : p+s • g ∈ halfspaces a b := by
    rw [hdecomp]
    exact ⟨p,hp,s,hs,le_rfl,rfl⟩
  have hb0 := hp0 j
  have hb1 := hp1 i
  have hix := congrArg (fun z : E => a i z) hxpt
  have hjx := congrArg (fun z : E => a j z) hxpt
  simp only [map_add,map_smul,smul_eq_mul] at hb1 hix hjx
  have hfirst : t*(-a j g) ≤ b j-a j x := by nlinarith
  have hlast : (s-t)*(a i g) ≤ b i-a i x := by nlinarith
  have h₁ := mul_le_mul_of_nonneg_left hfirst hi.le
  have h₂ := mul_le_mul_of_nonneg_left hlast (le_of_lt (neg_pos.mpr hj))
  have hprod : 0 < (a i g)*(-a j g) := mul_pos hi (neg_pos.mpr hj)
  nlinarith [h₁,h₂,hsharp,hprod]

end HirschSegmentSharpPublic
end

theorem solution
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι]
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g x : E) (τ s : ℝ)
    (i j : ι) (hi : 0 < a i g) (hj : a j g < 0)
    (hx : x ∈ HirschSegmentSharpPublic.halfspaces a b)
    (hsharp : (-a j g)*(b i-a i x)+(a i g)*(b j-a j x) = τ*(a i g)*(-a j g))
    (P : Set E) (hs : 0 ≤ s)
    (hdecomp : HirschSegmentSharpPublic.halfspaces a b =
      HirschSegmentSharpPublic.segmentSum P g s) : s ≤ τ := by
  exact HirschSegmentSharpPublic.any_segment_summand_le_sharp_width
    a b g x τ s i j hi hj hx hsharp P hs hdecomp

#print axioms solution
