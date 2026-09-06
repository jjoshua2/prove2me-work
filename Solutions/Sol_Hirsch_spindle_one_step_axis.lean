import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_wedge
import Theorems.Thm_Hirsch_spindle_perturbed_wedge_is_spindle
import Theorems.Thm_Hirsch_spindle_perturbed_wedge_length

open scoped RealInnerProductSpace
open Set Hirsch

theorem solution (d n : ℕ) (hd : 0 < d) (hn : 2 * d < n)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (i0 : Fin n)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ) ∈
      Set.extremePoints ℝ (Hpoly a b))
    (hv : EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (-1 : ℝ) ∈
      Set.extremePoints ℝ (Hpoly a b))
    (hspindle : ∀ i,
      (⟪a i, EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ)⟫ = b i) ↔
        ⟪a i, EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (-1 : ℝ)⟫ ≠ b i)
    (htight : ⟪a i0, EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ)⟫ = b i0)
    (hlong : ∀ w : ℕ → EuclideanSpace ℝ (Fin d),
      ¬ (w 0 = EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ) ∧
          w d = EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (-1 : ℝ) ∧
          ∀ j < d, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)))) :
    ∃ (a' : Fin (n + 1) → EuclideanSpace ℝ (Fin (d + 1)))
      (b' : Fin (n + 1) → ℝ)
      (u' v' : EuclideanSpace ℝ (Fin (d + 1))),
      (Hpoly a' b').Nonempty ∧
      Bornology.IsBounded (Hpoly a' b') ∧
      u' ∈ Set.extremePoints ℝ (Hpoly a' b') ∧
      v' ∈ Set.extremePoints ℝ (Hpoly a' b') ∧
      (∀ i, (⟪a' i, u'⟫ = b' i) ↔ ⟪a' i, v'⟫ ≠ b' i) ∧
      ∀ w : ℕ → EuclideanSpace ℝ (Fin (d + 1)),
        ¬ (w 0 = u' ∧ w (d + 1) = v' ∧
            ∀ j < d + 1, w j = w (j + 1) ∨
              Adj (Hpoly a' b') (w j) (w (j + 1))) := by
  obtain ⟨i1, ε, a', b', u', v', hε, ha', hb', hu', hv', hne', hbd', huP, hvP, hsp'⟩ :=
    spindle_perturbed_wedge_is_spindle d n hd hn a b i0 hne hbd hu hv hspindle htight
  have hlong' :=
    spindle_perturbed_wedge_length d n hd hn a b i0 i1 ε a' b' u' v'
      hε ha' hb' hu' hv' hlong
  exact ⟨a', b', u', v', hne', hbd', huP, hvP, hsp', hlong'⟩
