import Mathlib
import Solutions.AxisSymExtremes
import Solutions.AxisSideSelection

open scoped RealInnerProductSpace
open Set WithLp EuclideanSpace Hirsch

noncomputable section

namespace HirschAxisSymSelect

variable {d n : ℕ}

/-- Select the source-valid wedge foot on one spindle side and a removable
active facet on the nonsimple side.  For every nonzero tilt, the symmetric
perturbed wedge has the two height-zero lifted apices as extreme points and
preserves the spindle XOR. -/
theorem choose_structural_perturbation
    (hn : 2 * d < n)
    (c : Fin n → EuclideanSpace ℝ (Fin d))
    (u v : EuclideanSpace ℝ (Fin d))
    (hUle : ∀ i, ⟪c i, u⟫ ≤ 1)
    (hVle : ∀ i, ⟪c i, v⟫ ≤ 1)
    (hxor : ∀ i, (⟪c i, u⟫ = 1) ↔ ⟪c i, v⟫ ≠ 1)
    (hUzero : ∀ y : EuclideanSpace ℝ (Fin d),
      (∀ i, ⟪c i, u⟫ = 1 → ⟪c i, y⟫ = 0) → y = 0)
    (hVzero : ∀ y : EuclideanSpace ℝ (Fin d),
      (∀ i, ⟪c i, v⟫ = 1 → ⟪c i, y⟫ = 0) → y = 0)
    (fU : Fin n) (hfU : ⟪c fU, u⟫ = 1)
    (hVexists : ∃ i, ⟪c i, v⟫ = 1) :
    ∃ f g : Fin n,
      ∀ ε : ℝ, ε ≠ 0 →
        let A := HirschAxisSym.symPerturbA c f g ε
        let B := HirschAxisSym.symPerturbB (n := n)
        let U := Hirsch.embed u 0
        let V := Hirsch.embed v 0
        U ∈ extremePoints ℝ (Hpoly A B) ∧
        V ∈ extremePoints ℝ (Hpoly A B) ∧
        (∀ j, (⟪A j, U⟫ = B j) ↔ ⟪A j, V⟫ ≠ B j) := by
  classical
  let SU : Finset (Fin n) := Finset.univ.filter (fun i => ⟪c i, u⟫ = 1)
  let SV : Finset (Fin n) := Finset.univ.filter (fun i => ⟪c i, v⟫ = 1)
  have hdisj : Disjoint SU SV := by
    refine Finset.disjoint_left.2 ?_
    intro i hiU hiV
    have hUi : ⟪c i, u⟫ = 1 := (Finset.mem_filter.1 hiU).2
    have hVi : ⟪c i, v⟫ = 1 := (Finset.mem_filter.1 hiV).2
    exact (hxor i).1 hUi hVi
  have hcover : SU ∪ SV = Finset.univ := by
    apply Finset.eq_univ_iff_forall.2
    intro i
    by_cases hUi : ⟪c i, u⟫ = 1
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ i, hUi⟩)
    · have hVi : ⟪c i, v⟫ = 1 := by
        by_contra hVnot
        exact hUi ((hxor i).2 hVnot)
      exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ i, hVi⟩)
  have hUz : ∀ y : EuclideanSpace ℝ (Fin d),
      (∀ i, i ∈ SU → ⟪c i, y⟫ = 0) → y = 0 := by
    intro y hy
    apply hUzero y
    intro i hi
    exact hy i (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩)
  have hVz : ∀ y : EuclideanSpace ℝ (Fin d),
      (∀ i, i ∈ SV → ⟪c i, y⟫ = 0) → y = 0 := by
    intro y hy
    apply hVzero y
    intro i hi
    exact hy i (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩)
  have hfUmem : fU ∈ SU := Finset.mem_filter.2 ⟨Finset.mem_univ fU, hfU⟩
  have hSVne : SV.Nonempty := by
    obtain ⟨i, hi⟩ := hVexists
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨f, g, hcase⟩ :=
    HirschAxisSelect.choose_foot_and_removable hn c SU SV hdisj hcover hUz hVz fU hfUmem hSVne
  refine ⟨f, g, ?_⟩
  intro ε hε
  dsimp
  have hinc := HirschAxisSym.sym_spindle_incidence c u v f g ε hUle hVle hxor
  rcases hinc with ⟨hUmem, hVmem, hnewxor⟩
  rcases hcase with hVlarge | hUlarge
  · rcases hVlarge with ⟨hfSU, hgSV, hremV⟩
    have hf : ⟪c f, u⟫ = 1 := (Finset.mem_filter.1 hfSU).2
    have hfvnot : ⟪c f, v⟫ ≠ 1 := (hxor f).1 hf
    have hg : ⟪c g, v⟫ = 1 := (Finset.mem_filter.1 hgSV).2
    have hgunot : ⟪c g, u⟫ ≠ 1 := by
      intro hgu
      exact (hxor g).1 hgu hg
    have hremV' : ∀ y : EuclideanSpace ℝ (Fin d),
        (∀ i, ⟪c i, v⟫ = 1 → i ≠ g → ⟪c i, y⟫ = 0) → y = 0 := by
      intro y hy
      apply hremV y
      intro i hiSV hig
      exact hy i (Finset.mem_filter.1 hiSV).2 hig
    have hUext := HirschAxisSym.foot_apex_extreme c f g ε u hUle hf hgunot hUzero
    have hVext := HirschAxisSym.perturbed_apex_extreme c f g ε v hVle hg hfvnot hε hremV'
    exact ⟨hUext, hVext, hnewxor⟩
  · rcases hUlarge with ⟨hfSV, hgSU, hremU⟩
    have hf : ⟪c f, v⟫ = 1 := (Finset.mem_filter.1 hfSV).2
    have hfunot : ⟪c f, u⟫ ≠ 1 := by
      intro hfu
      exact (hxor f).1 hfu hf
    have hg : ⟪c g, u⟫ = 1 := (Finset.mem_filter.1 hgSU).2
    have hgvnot : ⟪c g, v⟫ ≠ 1 := (hxor g).1 hg
    have hremU' : ∀ y : EuclideanSpace ℝ (Fin d),
        (∀ i, ⟪c i, u⟫ = 1 → i ≠ g → ⟪c i, y⟫ = 0) → y = 0 := by
      intro y hy
      apply hremU y
      intro i hiSU hig
      exact hy i (Finset.mem_filter.1 hiSU).2 hig
    have hVext := HirschAxisSym.foot_apex_extreme c f g ε v hVle hf hgvnot hVzero
    have hUext := HirschAxisSym.perturbed_apex_extreme c f g ε u hUle hg hfunot hε hremU'
    exact ⟨hUext, hVext, hnewxor⟩

end HirschAxisSymSelect
