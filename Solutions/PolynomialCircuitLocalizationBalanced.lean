import Mathlib
import Solutions.PolynomialCircuitLocalization

open scoped RealInnerProductSpace
open Set Module Hirsch

noncomputable section

namespace HirschCircuitLocalization

/-- In an exactly balanced `n = 2*d` presentation of dimension at least two,
a vertex-to-vertex row-circuit displacement cannot be estranged: the two
vertices share a nonzero describing row that is tight at both endpoints. -/
theorem balanced_rowCircuit_vertices_share_nonzero_tight_row
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbal : n = 2 * d) (hd : 2 ≤ d)
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u)) :
    ∃ i : Fin n, a i ≠ 0 ∧ ⟪a i, u⟫ = b i ∧ ⟪a i, v⟫ = b i := by
  classical
  by_contra hnone
  have hC : HirschPolynomialAccess.commonSourceRows a b u v = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro i hi
    have h := (Finset.mem_filter.1 hi).2
    exact hnone ⟨i, h.1, h.2.1, h.2.2⟩
  have hdir : HirschPolynomialAccess.commonDirection a b u v =
      (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin d))) := by
    ext q
    simp [HirschPolynomialAccess.commonDirection,
      HirschPolynomialAccess.rowEvalMap, hC]
  have hdim : HirschPolynomialAccess.commonFaceDim a b u v = d := by
    rw [HirschPolynomialAccess.commonFaceDim, hdir]
    simp
  have hloc := rowCircuit_commonFaceDim_localization a b u v hu hv hcirc
  rw [hdim] at hloc
  omega

#print axioms balanced_rowCircuit_vertices_share_nonzero_tight_row

end HirschCircuitLocalization
