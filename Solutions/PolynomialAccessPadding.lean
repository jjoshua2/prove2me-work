import Mathlib
import Definitions.Def_Hirsch_model
import Theorems.Thm_Hirsch_larman_bound
import Solutions.PolynomialFaceAccessBench

open scoped RealInnerProductSpace
open Set Hirsch

namespace HirschPolynomialAccess

/-- `DiamLE` is monotone in its step budget because stationary steps are
allowed.  We pad a shorter walk by freezing it at its endpoint. -/
lemma diamLE_mono {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Set E) {B B' : ℕ} (hBB' : B ≤ B')
    (hD : DiamLE P B) : DiamLE P B' := by
  intro u hu v hv
  obtain ⟨w, hw0, hwB, hwstep⟩ := hD u hu v hv
  let w' : ℕ → E := fun j => w (min j B)
  refine ⟨w', ?_, ?_, ?_⟩
  · simpa [w'] using hw0
  · have hmin : min B' B = B := Nat.min_eq_right hBB'
    simpa [w', hmin] using hwB
  · intro j hj
    by_cases hjB : j < B
    · have hjle : j ≤ B := Nat.le_of_lt hjB
      have hsuccle : j + 1 ≤ B := by omega
      simpa [w', Nat.min_eq_left hjle, Nat.min_eq_left hsuccle] using hwstep j hjB
    · have hBj : B ≤ j := by omega
      have hBsucc : B ≤ j + 1 := by omega
      exact Or.inl (by simp [w', Nat.min_eq_right hBj, Nat.min_eq_right hBsucc])

/-- Larman already proves a quadratic specified-face access bound on the
regime `2^(d-3) ≤ n`.  Thus the genuinely open part of the polynomial leaf can
be restricted to the complementary high-dimensional regime. -/
lemma larman_easy_regime_given_face_access (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    {u v : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hreg : 2 ^ (d - 3) ≤ n)
    (i : Fin n) (hiv : ⟪a i, v⟫ = b i) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w ((n + d) ^ 2) = z ∧
        ∀ j < (n + d) ^ 2,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  have hne : (Hpoly a b).Nonempty := ⟨u, hu.1⟩
  have hL : DiamLE (Hpoly a b) (n * 2 ^ (d - 3)) :=
    Hirsch.larman_bound d n a b hne hbd
  have hbudget : n * 2 ^ (d - 3) ≤ (n + d) ^ 2 := by
    have h1 : n * 2 ^ (d - 3) ≤ n * n := Nat.mul_le_mul_left n hreg
    have h2 : n * n ≤ (n + d) ^ 2 := by
      simp [pow_two]
      nlinarith
    exact h1.trans h2
  exact given_face_access_of_diamLE a b hu hv
    (diamLE_mono (Hpoly a b) hbudget hL) i hiv

end HirschPolynomialAccess
