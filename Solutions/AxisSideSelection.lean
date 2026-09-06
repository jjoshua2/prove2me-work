import Mathlib
import Solutions.AxisActive

open scoped RealInnerProductSpace
open Set WithLp EuclideanSpace Hirsch

noncomputable section

namespace HirschAxisSelect

variable {d n : ℕ}

/-- If two disjoint active sets cover all rows and there are more than `2d`
rows, one side has more than `d` rows.  Choose a removable row on that side
and a foot row on the opposite side. -/
lemma choose_foot_and_removable
    (hn : 2 * d < n)
    (c : Fin n → EuclideanSpace ℝ (Fin d))
    (SU SV : Finset (Fin n))
    (hdisj : Disjoint SU SV)
    (hcover : SU ∪ SV = Finset.univ)
    (hUzero : ∀ y : EuclideanSpace ℝ (Fin d),
      (∀ i, i ∈ SU → ⟪c i, y⟫ = 0) → y = 0)
    (hVzero : ∀ y : EuclideanSpace ℝ (Fin d),
      (∀ i, i ∈ SV → ⟪c i, y⟫ = 0) → y = 0)
    (fU : Fin n) (hfU : fU ∈ SU)
    (hSVne : SV.Nonempty) :
    ∃ f g : Fin n,
      (f ∈ SU ∧ g ∈ SV ∧
        (∀ y : EuclideanSpace ℝ (Fin d),
          (∀ i, i ∈ SV → i ≠ g → ⟪c i, y⟫ = 0) → y = 0)) ∨
      (f ∈ SV ∧ g ∈ SU ∧
        (∀ y : EuclideanSpace ℝ (Fin d),
          (∀ i, i ∈ SU → i ≠ g → ⟪c i, y⟫ = 0) → y = 0)) := by
  classical
  have hinter : SU ∩ SV = ∅ := Finset.disjoint_iff_inter_eq_empty.1 hdisj
  have hsum : SU.card + SV.card = n := by
    have hcard := Finset.card_union_add_card_inter SU SV
    rw [hcover, hinter] at hcard
    simpa using hcard
  by_cases hVlarge : d < SV.card
  · obtain ⟨g, hgV, hrem⟩ :=
      HirschAxisActive.exists_removable_active c SV hVlarge hVzero
    exact ⟨fU, g, Or.inl ⟨hfU, hgV, hrem⟩⟩
  · have hVsmall : SV.card ≤ d := by omega
    have hUlarge : d < SU.card := by omega
    obtain ⟨g, hgU, hrem⟩ :=
      HirschAxisActive.exists_removable_active c SU hUlarge hUzero
    obtain ⟨f, hfV⟩ := hSVne
    exact ⟨f, g, Or.inr ⟨hfV, hgU, hrem⟩⟩

end HirschAxisSelect
