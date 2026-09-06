import Mathlib
import Definitions.Def_Hirsch_model
import Theorems.Thm_Hirsch_larman_bound
import Theorems.Thm_Hirsch_dimension_three_bound

open scoped RealInnerProductSpace
open Set Hirsch

namespace HirschPolynomialAccess

/-- In the actual open leaf, the prescribed target facet is necessarily
strictly absent from the source vertex: `hsep` plus nonzero support and
`tight at v` rules out `tight at u`. -/
lemma source_not_on_given_face {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hsep : ∀ j, a j ≠ 0 →
      ⟪a j, u⟫ ≠ b j ∨ ⟪a j, v⟫ ≠ b j)
    (i : Fin n) (hai : a i ≠ 0) (hiv : ⟪a i, v⟫ = b i) :
    ⟪a i, u⟫ ≠ b i := by
  rcases hsep i hai with hiu | hiv'
  · exact hiu
  · exact False.elim (hiv' hiv)

/-- Any diameter bound immediately gives access to a specified supporting
face: simply choose the target vertex itself.  This is the exact adapter that
turns known global bounds into baselines for the remaining open leaf. -/
lemma given_face_access_of_diamLE {d n B : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {u v : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hD : DiamLE (Hpoly a b) B)
    (i : Fin n) (hiv : ⟪a i, v⟫ = b i) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w B = z ∧
        ∀ j < B,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  obtain ⟨w, hw0, hwB, hwalk⟩ := hD u hu v hv
  exact ⟨v, hv, hiv, w, hw0, hwB, hwalk⟩

/-- Larman gives an unconditional exponential-in-d specified-face access
baseline.  This is not polynomial and is not a solution of the open leaf. -/
lemma larman_given_face_access (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    {u v : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (i : Fin n) (hiv : ⟪a i, v⟫ = b i) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (n * 2 ^ (d - 3)) = z ∧
        ∀ j < n * 2 ^ (d - 3),
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  have hne : (Hpoly a b).Nonempty := ⟨u, hu.1⟩
  exact given_face_access_of_diamLE a b hu hv
    (Hirsch.larman_bound d n a b hne hbd) i hiv

/-- In ambient dimension at most three the specified-face access problem is
already linear, by the proved low-dimensional Hirsch bound. -/
lemma dimension_three_given_face_access (d n : ℕ) (hd : d ≤ 3)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    {u v : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (i : Fin n) (hiv : ⟪a i, v⟫ = b i) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (n - d) = z ∧
        ∀ j < n - d,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  have hne : (Hpoly a b).Nonempty := ⟨u, hu.1⟩
  exact given_face_access_of_diamLE a b hu hv
    (Hirsch.dimension_three_bound d n hd a b hne hbd) i hiv

end HirschPolynomialAccess
