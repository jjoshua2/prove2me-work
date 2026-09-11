import Mathlib
import Solutions.PolynomialOneRowDeletionFarCapLevel
import Solutions.PolynomialHorizonCap

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschDeletion

/-- The H-polyhedron obtained by deleting one distinguished row, indexed by the
remaining original rows.  This presentation is convenient for reusing the
generic horizon-cap lemmas. -/
def deletionOuter
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (j : Fin n) : Set (EuclideanSpace ℝ (Fin d)) :=
  Hpoly
    (fun i : {i : Fin n // i ≠ j} => a i.1)
    (fun i : {i : Fin n // i ≠ j} => b i.1)

/-- Ordinary halfspace normal representing the explicit negative-row-sum cap
functional. -/
noncomputable def deletionCapNormal
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (j : Fin n) :
    EuclideanSpace ℝ (Fin d) :=
  -∑ i : {i : Fin n // i ≠ j}, a i.1

/-- The scalar cap functional is exactly evaluation against the ordinary cap
normal.  This is the vocabulary bridge needed by `HirschHorizon`. -/
theorem deletionCapNormal_inner
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (j : Fin n)
    (x : EuclideanSpace ℝ (Fin d)) :
    ⟪deletionCapNormal a j, x⟫ = deletionCapValue a j x := by
  classical
  simp [deletionCapNormal, deletionCapValue]

/-- The one-row deletion outer is convex. -/
theorem deletionOuter_convex
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (j : Fin n) : Convex ℝ (deletionOuter a b j) := by
  intro x hx y hy α β hα hβ hsum
  change ∀ i : {i : Fin n // i ≠ j},
    ⟪a i.1, α • x + β • y⟫ ≤ b i.1
  intro i
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  have hx' := hx i
  have hy' := hy i
  have hxa := mul_le_mul_of_nonneg_left hx' hα
  have hyb := mul_le_mul_of_nonneg_left hy' hβ
  have hb : α * b i.1 + β * b i.1 = b i.1 := by
    rw [← add_mul, hsum, one_mul]
  linarith

/-- The explicit capped deletion outer is literally the generic horizon cap of
the deletion outer by `deletionCapNormal`. -/
theorem deletionCappedOuter_eq_horizonCap
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (j : Fin n) (M : ℝ) :
    deletionCappedOuter a b j M =
      HirschHorizon.cap (deletionOuter a b j) (deletionCapNormal a j) M := by
  ext x
  change
    ((∀ i : Fin n, i ≠ j → ⟪a i, x⟫ ≤ b i) ∧
      deletionCapValue a j x ≤ M) ↔
    ((∀ i : {i : Fin n // i ≠ j}, ⟪a i.1, x⟫ ≤ b i.1) ∧
      ⟪deletionCapNormal a j, x⟫ ≤ M)
  constructor
  · rintro ⟨hrows, hcap⟩
    refine ⟨?_, ?_⟩
    · intro i
      exact hrows i.1 i.2
    · rw [deletionCapNormal_inner]
      exact hcap
  · rintro ⟨hrows, hcap⟩
    refine ⟨?_, ?_⟩
    · intro i hij
      exact hrows ⟨i, hij⟩
    · rw [← deletionCapNormal_inner]
      exact hcap

/-- Every vertex of the explicit capped deletion outer is either an old vertex
of the uncapped deletion outer or lies on the cap horizon.  No ray
classification is needed for this first dichotomy. -/
theorem deletionCappedOuter_vertex_old_or_horizon
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (j : Fin n) (M : ℝ)
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ extremePoints ℝ (deletionCappedOuter a b j M)) :
    x ∈ extremePoints ℝ (deletionOuter a b j) ∨
      deletionCapValue a j x = M := by
  have hx' : x ∈ extremePoints ℝ
      (HirschHorizon.cap (deletionOuter a b j) (deletionCapNormal a j) M) := by
    rw [← deletionCappedOuter_eq_horizonCap a b j M]
    exact hx
  rcases HirschHorizon.cap_vertex_old_or_horizon
      (deletionOuter a b j) (deletionOuter_convex a b j)
      (deletionCapNormal a j) M hx' with hold | hhor
  · exact Or.inl hold
  · right
    rw [← deletionCapNormal_inner]
    exact hhor

/-- Along any capped-deletion vertex walk which starts strictly below the cap
and ends on the horizon, the first horizon crossing is an actual capped edge
from an old deletion-outer vertex.  This is the exact historical portal lemma
now specialized to the explicit universal deletion cap. -/
theorem deletionCappedOuter_first_horizon_edge
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (j : Fin n) (M : ℝ)
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hverts : ∀ k ≤ L, w k ∈ extremePoints ℝ (deletionCappedOuter a b j M))
    (hstep : ∀ k < L,
      w k = w (k + 1) ∨
        Adj (deletionCappedOuter a b j M) (w k) (w (k + 1)))
    (hstart : deletionCapValue a j (w 0) < M)
    (hend : deletionCapValue a j (w L) = M) :
    ∃ x y,
      x ∈ extremePoints ℝ (deletionOuter a b j) ∧
      y ∈ deletionCappedOuter a b j M ∧
      deletionCapValue a j y = M ∧
      Adj (deletionCappedOuter a b j M) x y := by
  have hverts' : ∀ k ≤ L, w k ∈ extremePoints ℝ
      (HirschHorizon.cap (deletionOuter a b j) (deletionCapNormal a j) M) := by
    intro k hk
    rw [← deletionCappedOuter_eq_horizonCap a b j M]
    exact hverts k hk
  have hstep' : ∀ k < L,
      w k = w (k + 1) ∨
        Adj (HirschHorizon.cap (deletionOuter a b j)
          (deletionCapNormal a j) M) (w k) (w (k + 1)) := by
    intro k hk
    rw [← deletionCappedOuter_eq_horizonCap a b j M]
    exact hstep k hk
  have hstart' : ⟪deletionCapNormal a j, w 0⟫ < M := by
    rw [deletionCapNormal_inner]
    exact hstart
  have hend' : ⟪deletionCapNormal a j, w L⟫ = M := by
    rw [deletionCapNormal_inner]
    exact hend
  obtain ⟨x, y, hx, hy, hyhor, hxy⟩ :=
    HirschHorizon.first_horizon_edge
      (deletionOuter a b j) (deletionOuter_convex a b j)
      (deletionCapNormal a j) M w L hverts' hstep' hstart' hend'
  refine ⟨x, y, hx, ?_, ?_, ?_⟩
  · rw [deletionCappedOuter_eq_horizonCap a b j M]
    exact hy
  · rw [← deletionCapNormal_inner]
    exact hyhor
  · rw [deletionCappedOuter_eq_horizonCap a b j M]
    exact hxy

#print axioms deletionCapNormal_inner
#print axioms deletionCappedOuter_eq_horizonCap
#print axioms deletionCappedOuter_vertex_old_or_horizon
#print axioms deletionCappedOuter_first_horizon_edge

end HirschDeletion
