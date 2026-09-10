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
  let SU : Finset (Fin n) :=
    Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, u⟫ = b i)
  let SV : Finset (Fin n) :=
    Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, v⟫ = b i)
  let Z := circuitNeutralRows a (v - u)
  have hU : d ≤ SU.card := by
    simpa [SU] using
      HirschPolynomialAccess.nonzero_tight_rows_card_ge_dim a b u hu
  have hV : d ≤ SV.card := by
    simpa [SV] using
      HirschPolynomialAccess.nonzero_tight_rows_card_ge_dim a b v hv
  have hZ : d - 1 ≤ Z.card := by
    simpa [Z] using
      circuitNeutralRows_card_ge_dim_sub_one a b u (v - u) hu hcirc
  have hUV : Disjoint SU SV := by
    refine Finset.disjoint_left.2 ?_
    intro i hiU hiV
    have hurow := (Finset.mem_filter.1 hiU).2
    have hvrow := (Finset.mem_filter.1 hiV).2
    exact hnone ⟨i, hurow.1, hurow.2, hvrow.2⟩
  have hUZ : Disjoint SU Z := by
    refine Finset.disjoint_left.2 ?_
    intro i hiU hiZ
    have hurow := (Finset.mem_filter.1 hiU).2
    have hzrow := (Finset.mem_filter.1 hiZ).2
    have hz0 : ⟪a i, v - u⟫ = 0 := hzrow.2
    rw [inner_sub_right] at hz0
    have hvEq : ⟪a i, v⟫ = b i := by linarith [hurow.2]
    exact hnone ⟨i, hurow.1, hurow.2, hvEq⟩
  have hVZ : Disjoint SV Z := by
    refine Finset.disjoint_left.2 ?_
    intro i hiV hiZ
    have hvrow := (Finset.mem_filter.1 hiV).2
    have hzrow := (Finset.mem_filter.1 hiZ).2
    have hz0 : ⟪a i, v - u⟫ = 0 := hzrow.2
    rw [inner_sub_right] at hz0
    have huEq : ⟪a i, u⟫ = b i := by linarith [hvrow.2]
    exact hnone ⟨i, hvrow.1, huEq, hvrow.2⟩
  have hUVZ : Disjoint (SU ∪ SV) Z :=
    Finset.disjoint_union_left.2 ⟨hUZ, hVZ⟩
  have htotal : (SU ∪ SV ∪ Z).card ≤ n := by
    have hsub : SU ∪ SV ∪ Z ⊆ (Finset.univ : Finset (Fin n)) := by simp
    calc
      (SU ∪ SV ∪ Z).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card hsub
      _ = n := by simp
  rw [Finset.card_union_of_disjoint hUVZ,
      Finset.card_union_of_disjoint hUV] at htotal
  omega

#print axioms balanced_rowCircuit_vertices_share_nonzero_tight_row

end HirschCircuitLocalization
