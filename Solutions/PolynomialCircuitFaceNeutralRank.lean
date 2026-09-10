import Mathlib
import Solutions.PolynomialCircuitNeutralRank

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCircuitLocalization

open HirschPolynomialAccess

variable {d n : ℕ}

/-- Restricting all ambient neutral rows of a row circuit to any subspace that
contains the circuit direction leaves exactly the same one-dimensional kernel,
now viewed inside that subspace. -/
theorem rowCircuit_neutral_kernel_on_subspace_eq_span
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u g : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hg : IsRowCircuit a g)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hgW : g ∈ W) :
    ((rowEvalMap a (circuitNeutralRows a g)).domRestrict W).ker =
      Submodule.span ℝ
        ({⟨g, hgW⟩} : Set W) := by
  classical
  let R := rowEvalMap a (circuitNeutralRows a g)
  let gw : W := ⟨g, hgW⟩
  have hamb : R.ker =
      Submodule.span ℝ ({g} : Set (EuclideanSpace ℝ (Fin d))) := by
    simpa [R] using rowCircuit_neutral_kernel_eq_span a b u g hu hg
  apply le_antisymm
  · intro x hx
    have hxamb : (x : EuclideanSpace ℝ (Fin d)) ∈ R.ker := by
      apply LinearMap.mem_ker.2
      have hx0 := LinearMap.mem_ker.1 hx
      simpa [R] using hx0
    rw [hamb] at hxamb
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxamb
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    apply Subtype.ext
    simpa [gw] using hc
  · apply Submodule.span_le.2
    intro x hx
    have hxgw : x = gw := by simpa [gw] using hx
    subst x
    apply LinearMap.mem_ker.2
    funext i
    change ⟪a i.1, g⟫ = 0
    exact (Finset.mem_filter.1 i.2).2.2

/-- Rank form of `rowCircuit_neutral_kernel_on_subspace_eq_span`: on every
subspace containing the circuit direction, the ambient neutral rows have rank
exactly one less than the dimension of that subspace. -/
theorem rowCircuit_neutral_rank_on_subspace_eq_dim_sub_one
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u g : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hg : IsRowCircuit a g)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hgW : g ∈ W) :
    Module.finrank ℝ
        (((rowEvalMap a (circuitNeutralRows a g)).domRestrict W).range) =
      Module.finrank ℝ W - 1 := by
  let T := (rowEvalMap a (circuitNeutralRows a g)).domRestrict W
  let gw : W := ⟨g, hgW⟩
  have hker : T.ker = Submodule.span ℝ ({gw} : Set W) := by
    simpa [T, gw] using
      rowCircuit_neutral_kernel_on_subspace_eq_span a b u g hu hg W hgW
  have hgw0 : gw ≠ 0 := by
    intro h
    apply hg.1
    have hv := congrArg Subtype.val h
    simpa [gw] using hv
  have hkerRank : Module.finrank ℝ T.ker = 1 := by
    rw [hker]
    exact finrank_span_singleton hgw0
  have hrank := T.finrank_range_add_finrank_ker
  rw [hkerRank] at hrank
  have hrank' := congrArg (fun m : ℕ => m - 1) hrank
  simpa using hrank'

/-- Central rank fact for intrinsic common-face restriction. If `v-u` is an
ambient row circuit based at the vertex `u`, then all ambient rows neutral on
that displacement, restricted to the direction space of the minimal common
face of `u` and `v`, have rank exactly `commonFaceDim - 1`.

This is the rank-preservation input used before deleting intrinsically
redundant restricted inequalities in the circuit-defect accounting argument. -/
theorem rowCircuit_neutral_rank_on_commonDirection_eq_commonFaceDim_sub_one
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u)) :
    Module.finrank ℝ
        (((rowEvalMap a (circuitNeutralRows a (v - u))).domRestrict
          (commonDirection a b u v)).range) =
      commonFaceDim a b u v - 1 := by
  have hgW : v - u ∈ commonDirection a b u v := by
    apply LinearMap.mem_ker.2
    funext i
    have hi := (Finset.mem_filter.1 i.2).2
    change ⟪a i.1, v - u⟫ = 0
    rw [inner_sub_right, hi.2.2, hi.2.1, sub_self]
  simpa [commonFaceDim] using
    rowCircuit_neutral_rank_on_subspace_eq_dim_sub_one
      a b u (v - u) hu hcirc (commonDirection a b u v) hgW

#print axioms rowCircuit_neutral_kernel_on_subspace_eq_span
#print axioms rowCircuit_neutral_rank_on_subspace_eq_dim_sub_one
#print axioms rowCircuit_neutral_rank_on_commonDirection_eq_commonFaceDim_sub_one

end HirschCircuitLocalization
