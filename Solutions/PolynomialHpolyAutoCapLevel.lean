import Solutions.PolynomialHpolyExteriorCapTransfer
import Solutions.PolynomialVertexSpan

/-! Automatic choice of a sufficiently far canonical cap level.

Old H-polyhedron vertices are finite because their finite tight-row sets encode
them injectively.  The canonical cap functional is therefore bounded above on
old vertices, and is bounded above on any compact final clipped set. -/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRadial

noncomputable section
namespace HirschHpolyCap

variable {d n : ℕ}

/-- The finite set of H-rows tight at a point. -/
def activeRows
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ⟪a i, x⟫ = b i)

lemma activeRows_injOn_extreme
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Set.InjOn (activeRows a b) (extremePoints ℝ (Hpoly a b)) := by
  classical
  intro x hx y hy hrows
  have hdir : y - x = 0 :=
    HirschPolynomialAccess.vertex_tight_rows_span_checked d n a b x hx (y - x) (by
      intro i hi
      have hmem : i ∈ activeRows a b x := by simp [activeRows, hi]
      rw [hrows] at hmem
      have hiy : ⟪a i, y⟫ = b i := by simpa [activeRows] using hmem
      rw [inner_sub_right, hiy, hi, sub_self])
  exact (sub_eq_zero.mp hdir).symm

/-- A finite H-polyhedron representation has only finitely many extreme
vertices, even when the represented polyhedron is unbounded. -/
theorem extremePoints_hpoly_finite
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    (extremePoints ℝ (Hpoly a b)).Finite := by
  classical
  have himage :
      ((activeRows a b) '' extremePoints ℝ (Hpoly a b)).Finite := Set.toFinite _
  exact Set.Finite.of_finite_image himage (activeRows_injOn_extreme a b)

/-- Given any compact target set, one can choose a canonical cap level which is
weakly above every old H-vertex and strictly above every target point. -/
theorem exists_far_cap_level
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (P : Set (EuclideanSpace ℝ (Fin d))) (hPc : IsCompact P) :
    ∃ T : ℝ,
      (∀ x ∈ extremePoints ℝ (Hpoly a b), ⟪capNormal a, x⟫ ≤ T) ∧
      (∀ x ∈ P, ⟪capNormal a, x⟫ < T) := by
  let ell : EuclideanSpace ℝ (Fin d) → ℝ := fun x => ⟪capNormal a, x⟫
  have hOldFinite : (ell '' extremePoints ℝ (Hpoly a b)).Finite :=
    (extremePoints_hpoly_finite a b).image ell
  have hOldBdd : BddAbove (ell '' extremePoints ℝ (Hpoly a b)) := hOldFinite.bddAbove
  have hell : Continuous ell := by
    dsimp [ell]
    fun_prop
  have hPBdd : BddAbove (ell '' P) := hPc.bddAbove_image hell.continuousOn
  obtain ⟨Uold, hUold⟩ := bddAbove_def.mp hOldBdd
  obtain ⟨Up, hUp⟩ := bddAbove_def.mp hPBdd
  let T : ℝ := max Uold Up + 1
  refine ⟨T, ?_, ?_⟩
  · intro x hx
    have hxU : ell x ≤ Uold := hUold (ell x) ⟨x, hx, rfl⟩
    dsimp [ell, T] at hxU ⊢
    linarith [le_max_left Uold Up]
  · intro x hx
    have hxU : ell x ≤ Up := hUp (ell x) ⟨x, hx, rfl⟩
    dsimp [ell, T] at hxU ⊢
    linarith [le_max_right Uold Up]

#print axioms activeRows_injOn_extreme
#print axioms extremePoints_hpoly_finite
#print axioms exists_far_cap_level

end HirschHpolyCap
