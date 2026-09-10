import Definitions.Def_Hirsch_model
import Solutions.PolynomialSeparatedRows

open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch

theorem nonzero_supporting_row_of_distinct_extremes :
    ∀ (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hpoly a b) →
      ∀ u ∈ Set.extremePoints ℝ (Hpoly a b),
      ∀ v ∈ Set.extremePoints ℝ (Hpoly a b), u ≠ v →
      ∃ i : Fin n, a i ≠ 0 ∧ ⟪a i, v⟫ = b i := by
  intro d n a b _hbd u hu v hv huv
  have hdpos : 0 < d := by
    by_contra hd
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    subst d
    exact huv (Subsingleton.elim _ _)
  let S : Finset (Fin n) :=
    Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, v⟫ = b i)
  have hcard : d ≤ S.card := by
    simpa [S] using
      HirschPolynomialAccess.nonzero_tight_rows_card_ge_dim a b v hv
  have hSne : S.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hdpos hcard)
  obtain ⟨i, hiS⟩ := hSne
  have hi := (Finset.mem_filter.mp hiS).2
  exact ⟨i, hi.1, hi.2⟩

#print axioms nonzero_supporting_row_of_distinct_extremes

end Hirsch
