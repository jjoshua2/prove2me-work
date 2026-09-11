import Mathlib
import Solutions.PolynomialExcessTwoSupportFaces

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 3000000
set_option autoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschExcessTwo

/-- The normalized moment slice is convex. -/
theorem momentSlice_convex {n : ℕ} (t : Fin n → ℝ) (mu : ℝ) :
    Convex ℝ (momentSlice t mu) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change 0 ≤ a * x i + b * y i
    nlinarith [hx.1 i, hy.1 i]
  · change (∑ i, (a * x i + b * y i)) = 1
    calc
      (∑ i, (a * x i + b * y i)) =
          a * (∑ i, x i) + b * (∑ i, y i) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = a * 1 + b * 1 := by rw [hx.2.1, hy.2.1]
      _ = 1 := by nlinarith
  · change (∑ i, t i * (a * x i + b * y i)) = mu
    calc
      (∑ i, t i * (a * x i + b * y i)) =
          ∑ i, (a * (t i * x i) + b * (t i * y i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = a * (∑ i, t i * x i) + b * (∑ i, t i * y i) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = a * mu + b * mu := by rw [hx.2.2, hy.2.2]
      _ = mu := by nlinarith

/-- The segment between two points of one support carrier remains in that
support carrier. -/
theorem segment_subset_supportFace {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (S : Finset (Fin n))
    (x y : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ supportFace t mu S) (hy : y ∈ supportFace t mu S) :
    segment ℝ x y ⊆ supportFace t mu S := by
  intro z hz
  have hzP : z ∈ momentSlice t mu :=
    (momentSlice_convex t mu).segment_subset hx.1 hy.1 hz
  refine ⟨hzP, ?_⟩
  intro k hk
  rcases mem_segment_iff_div.mp hz with ⟨a, b, ha, hb, hab, hcomb⟩
  have hcoord := congrArg (fun q : EuclideanSpace ℝ (Fin n) => q k) hcomb
  have hx0 := hx.2 k hk
  have hy0 := hy.2 k hk
  simpa [hx0, hy0] using hcoord.symm

#print axioms momentSlice_convex
#print axioms segment_subset_supportFace

end HirschExcessTwo
