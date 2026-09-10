import Solutions.PolynomialCircuitCarrierRank
import Solutions.PolynomialCircuitNeutralRank

open scoped RealInnerProductSpace
open Set Module Hirsch

noncomputable section

namespace HirschPolynomialAccess

variable {d n : ℕ}

/-- Active defect is exactly carrier dimension minus one. This is an algebraic
identity valid even without feasibility, circuit, or extremality hypotheses. -/
theorem activeNeutralDefect_displacement_eq_commonFaceDim_sub_one
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    activeNeutralDefect a b x (y - x) = commonFaceDim a b x y - 1 := by
  unfold activeNeutralDefect
  rw [activeNeutralRows_displacement_eq_commonSourceRows]
  have arithmetic : ∀ r h D : ℕ, r + h = D → (D - 1) - r = h - 1 := by
    omega
  exact arithmetic _ _ _ (commonSource_rank_add_commonFaceDim a b x y)

/-- Zero active defect and a carrier of dimension at most one are equivalent.
This statement itself does not assert that either endpoint is a vertex. -/
theorem activeNeutralDefect_displacement_zero_iff
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    activeNeutralDefect a b x (y - x) = 0 ↔ commonFaceDim a b x y ≤ 1 := by
  rw [activeNeutralDefect_displacement_eq_commonFaceDim_sub_one]
  exact Nat.sub_eq_zero_iff_le

/-- Two distinct points give a nonzero direction in their common-tight kernel,
even before any feasibility hypothesis is imposed. -/
theorem commonFaceDim_pos_of_displacement_ne_zero
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) (hne : y - x ≠ 0) :
    0 < commonFaceDim a b x y := by
  have hg : y - x ∈ commonDirection a b x y := by
    apply LinearMap.mem_ker.2
    funext i
    have hi := (Finset.mem_filter.1 i.2).2
    change ⟪a i.1, y - x⟫ = 0
    rw [inner_sub_right, hi.2.2, hi.2.1, sub_self]
  have hspan : Submodule.span ℝ ({y - x} : Set (EuclideanSpace ℝ (Fin d))) ≤
      commonDirection a b x y := by
    apply Submodule.span_le.2
    intro z hz
    have heq : z = y - x := by simpa only [Set.mem_singleton_iff] using hz
    rw [heq]
    exact hg
  have hdim := Submodule.finrank_mono hspan
  rw [finrank_span_singleton hne] at hdim
  change 1 ≤ commonFaceDim a b x y at hdim
  exact lt_of_lt_of_le Nat.zero_lt_one hdim

/-- For a genuine displacement, carrier dimension is active defect plus one. -/
theorem activeNeutralDefect_add_one_eq_commonFaceDim
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) (hne : y - x ≠ 0) :
    activeNeutralDefect a b x (y - x) + 1 = commonFaceDim a b x y := by
  rw [activeNeutralDefect_displacement_eq_commonFaceDim_sub_one]
  exact Nat.sub_add_cancel (commonFaceDim_pos_of_displacement_ne_zero a b x y hne)

/-- For a row circuit based at a vertex, active defect is the rank lost by
restricting ALL neutral rows to those ACTIVE at that source. It is a rank
loss, not the cardinality of the inactive rows. -/
theorem rowCircuit_activeNeutralDefect_eq_neutral_rank_loss
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x g : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b)) (hg : IsRowCircuit a g) :
    activeNeutralDefect a b x g =
      Module.finrank ℝ
          (rowEvalMap a (HirschCircuitLocalization.circuitNeutralRows a g)).range -
        Module.finrank ℝ (rowEvalMap a (activeNeutralRows a b x g)).range := by
  rw [HirschCircuitLocalization.rowCircuit_neutral_rank_eq_dim_sub_one a b x g hx hg]
  rfl

/-- A vertex-start maximal circuit step which is not an edge has positive
active defect. The target need not be assumed to be a vertex. -/
theorem rowCircuitStep_nonadj_activeNeutralDefect_pos
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hstep : RowCircuitStep a b x y) (hnot : ¬ Adj (Hpoly a b) x y) :
    0 < activeNeutralDefect a b x (y - x) := by
  apply Nat.pos_of_ne_zero
  intro hz
  exact hnot (rowCircuitStep_adj_of_activeNeutralDefect_zero a b x y hx hstep hz)

/-- The sharp localization theorem charges TWO units of ambient row excess
for each unit of active carrier defect, in the vertex-to-vertex circuit case.
This statement deliberately does not cover nonvertex circuit intermediates. -/
theorem rowCircuit_vertex_pair_activeDefect_bound
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hy : y ∈ extremePoints ℝ (Hpoly a b)) (hg : IsRowCircuit a (y - x)) :
    2 * activeNeutralDefect a b x (y - x) + d + 1 ≤ n := by
  have hdim := activeNeutralDefect_add_one_eq_commonFaceDim a b x y hg.1
  have hloc := HirschCircuitLocalization.rowCircuit_commonFaceDim_localization a b x y hx hy hg
  have arithmetic : ∀ k h D N : ℕ,
      k + 1 = h → 2 * h + D ≤ N + 1 → 2 * k + D + 1 ≤ N := by omega
  exact arithmetic _ _ _ _ hdim hloc

/-- In row excess at most two, a vertex-to-vertex maximal circuit step is
already an ordinary edge. No simplicity or irredundancy assumption is used. -/
theorem rowCircuitStep_adj_of_row_excess_le_two
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hy : y ∈ extremePoints ℝ (Hpoly a b))
    (hstep : RowCircuitStep a b x y) (hrows : n ≤ d + 2) :
    Adj (Hpoly a b) x y := by
  have hcharge := rowCircuit_vertex_pair_activeDefect_bound a b x y hx hy hstep.2.2.1
  apply rowCircuitStep_adj_of_activeNeutralDefect_zero a b x y hx hstep
  have arithmetic : ∀ k D N : ℕ, 2 * k + D + 1 ≤ N → N ≤ D + 2 → k = 0 := by omega
  exact arithmetic _ _ _ hcharge hrows

#print axioms activeNeutralDefect_displacement_eq_commonFaceDim_sub_one
#print axioms activeNeutralDefect_displacement_zero_iff
#print axioms commonFaceDim_pos_of_displacement_ne_zero
#print axioms activeNeutralDefect_add_one_eq_commonFaceDim
#print axioms rowCircuit_activeNeutralDefect_eq_neutral_rank_loss
#print axioms rowCircuitStep_nonadj_activeNeutralDefect_pos
#print axioms rowCircuit_vertex_pair_activeDefect_bound
#print axioms rowCircuitStep_adj_of_row_excess_le_two

end HirschPolynomialAccess
