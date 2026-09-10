import Mathlib
import Solutions.PolynomialCircuitCarrierEdge

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 2500000

noncomputable section

namespace HirschPolynomialAccess

variable {d n : ℕ}

/-- Rows active at `x` whose normals are neutral to direction `g`.  For
`g = y - x`, these are exactly the nonzero rows active at both endpoints. -/
noncomputable def activeNeutralRows
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x g : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter fun i =>
    a i ≠ 0 ∧ ⟪a i, x⟫ = b i ∧ ⟪a i, g⟫ = 0

/-- Endpoint common-tight rows are exactly the rows active at the source and
neutral to the endpoint displacement. -/
theorem activeNeutralRows_displacement_eq_commonSourceRows
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    activeNeutralRows a b x (y - x) = commonSourceRows a b x y := by
  ext i
  simp only [activeNeutralRows, commonSourceRows, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hai, hix, hig⟩
    refine ⟨hai, hix, ?_⟩
    rw [inner_sub_right] at hig
    linarith
  · rintro ⟨hai, hix, hiy⟩
    refine ⟨hai, hix, ?_⟩
    rw [inner_sub_right, hiy, hix, sub_self]

/-- Rank-nullity conversion: if the common-tight rows have rank at least
`d-1` in subtraction-free form, then the common-face carrier has dimension
at most one. -/
theorem commonFaceDim_le_one_of_commonSource_rank
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hrank : d ≤ Module.finrank ℝ
      (rowEvalMap a (commonSourceRows a b x y)).range + 1) :
    commonFaceDim a b x y ≤ 1 := by
  let T := rowEvalMap a (commonSourceRows a b x y)
  have hrn := T.finrank_range_add_finrank_ker
  have hdom : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
    finrank_euclideanSpace_fin (𝕜 := ℝ)
  rw [hdom] at hrn
  have hsum :
      Module.finrank ℝ T.range + commonFaceDim a b x y = d := by
    simpa [T, commonFaceDim, commonDirection] using hrn
  change d ≤ Module.finrank ℝ T.range + 1 at hrank
  rw [← hsum] at hrank
  exact Nat.le_of_add_le_add_left hrank

/-- Rank form of the carrier criterion: a maximal row-circuit augmentation
from a vertex is a graph edge whenever its common-tight rows have rank at
least `d-1` (written without truncated subtraction). -/
theorem rowCircuitStep_adj_of_commonSource_rank
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hstep : RowCircuitStep a b x y)
    (hrank : d ≤ Module.finrank ℝ
      (rowEvalMap a (commonSourceRows a b x y)).range + 1) :
    Adj (Hpoly a b) x y := by
  apply rowCircuitStep_adj_of_commonFaceDim_le_one a b x y hx hstep
  exact commonFaceDim_le_one_of_commonSource_rank a b x y hrank

/-- Historical active-neutral formulation of the same criterion.  This is the
exact local rank test suggested by the circuit/edge obstruction analysis. -/
theorem rowCircuitStep_adj_of_activeNeutral_rank
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hstep : RowCircuitStep a b x y)
    (hrank : d ≤ Module.finrank ℝ
      (rowEvalMap a (activeNeutralRows a b x (y - x))).range + 1) :
    Adj (Hpoly a b) x y := by
  apply rowCircuitStep_adj_of_commonSource_rank a b x y hx hstep
  rw [← activeNeutralRows_displacement_eq_commonSourceRows a b x y]
  exact hrank

/-- Conventional `d-1` version of the active-neutral rank criterion. -/
theorem rowCircuitStep_adj_of_activeNeutral_rank_dim_sub_one
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hstep : RowCircuitStep a b x y)
    (hrank : d - 1 ≤ Module.finrank ℝ
      (rowEvalMap a (activeNeutralRows a b x (y - x))).range) :
    Adj (Hpoly a b) x y := by
  apply rowCircuitStep_adj_of_activeNeutral_rank a b x y hx hstep
  omega

/-- Defect of the active-neutral carrier from codimension one.  Zero defect
means the circuit augmentation is already a graph edge. -/
noncomputable def activeNeutralDefect
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x g : EuclideanSpace ℝ (Fin d)) : ℕ :=
  (d - 1) - Module.finrank ℝ (rowEvalMap a (activeNeutralRows a b x g)).range

/-- Zero active-neutral defect is exactly the easy circuit-to-edge case. -/
theorem rowCircuitStep_adj_of_activeNeutralDefect_zero
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hstep : RowCircuitStep a b x y)
    (hdef : activeNeutralDefect a b x (y - x) = 0) :
    Adj (Hpoly a b) x y := by
  apply rowCircuitStep_adj_of_activeNeutral_rank_dim_sub_one a b x y hx hstep
  change (d - 1) - Module.finrank ℝ
    (rowEvalMap a (activeNeutralRows a b x (y - x))).range = 0 at hdef
  exact Nat.sub_eq_zero_iff_le.mp hdef

#print axioms activeNeutralRows_displacement_eq_commonSourceRows
#print axioms commonFaceDim_le_one_of_commonSource_rank
#print axioms rowCircuitStep_adj_of_commonSource_rank
#print axioms rowCircuitStep_adj_of_activeNeutral_rank
#print axioms rowCircuitStep_adj_of_activeNeutral_rank_dim_sub_one
#print axioms rowCircuitStep_adj_of_activeNeutralDefect_zero

end HirschPolynomialAccess
