import Mathlib
import Definitions.Def_Hirsch_model
import Solutions.BoxSlicePivot
import Solutions.BoxSlicePotential
open Set Hirsch HirschBoxSlice
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace HirschBoxSlice
/-- A box intersected with one sum equality has graph diameter at most its
number of coordinates. Empty slices and zero-width coordinates are allowed. -/
theorem slice_diameter (d : ℕ) (cap : Fin d → ℝ) (total : ℝ) :
    DiamLE (slice cap total) d := by
  classical
  intro u hu v hv
  by_cases hd : d = 0
  · subst d
    have huv : u = v := Subsingleton.elim _ _
    exact ⟨fun _ => v, huv.symm, rfl, by omega⟩
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have hj : ∃ j : Fin d, ∀ k, k ≠ j → AtBound cap v k := by
      by_cases hf : ∃ k, Inside cap v k
      · obtain ⟨j, hj⟩ := hf
        exact ⟨j, bounds_except_inside cap total v hv.1 (regular_of_extreme cap total v hv) j hj⟩
      · let j : Fin d := ⟨0, hdpos⟩
        refine ⟨j, ?_⟩
        intro k hkj
        exact bound_of_not_inside cap total v hv.1 k (fun hk => hf ⟨k, hk⟩)
    obtain ⟨j, ht⟩ := hj
    exact walk_of_strict_potential (Adj (slice cap total))
      (fun x => x ∈ extremePoints ℝ (slice cap total)) v (potential cap v j)
      (fun x hx hne => decreasing_pivot cap total v j hv.1 ht x hx hne)
      d u hu (potential_le_dim cap v u j)
end HirschBoxSlice

/-- Exact publication statement. This is a restricted family theorem, not
the unrestricted polynomial Hirsch conjecture. -/
theorem solution (d : ℕ) (cap : Fin d → ℝ) (total : ℝ) :
    DiamLE {x : Fin d → ℝ | (∀ k, 0 ≤ x k ∧ x k ≤ cap k) ∧ ∑ k, x k = total} d := by
  exact HirschBoxSlice.slice_diameter d cap total

#print axioms HirschBoxSlice.decreasing_pivot
#print axioms solution
