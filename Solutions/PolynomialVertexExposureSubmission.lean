import Mathlib
import Definitions.Def_Hirsch_model
import Solutions.PolynomialVertexExposingRow

open scoped RealInnerProductSpace
open Set Hirsch HirschExposure

set_option maxHeartbeats 3000000

noncomputable section

/-- Add one redundant inequality exposing exactly v. The original inequalities,
polytope, and graph are unchanged; the added row is a target row, never neutral.
Endpoint separation is preserved. Thus prescribed supporting-row access may
literally require reaching v, even without adding any neutral normals. -/
theorem solution
    (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b)
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (huv : u ≠ v)
    (hsep : ∀ j, a j ≠ 0 → ⟪a j, u⟫ ≠ b j ∨ ⟪a j, v⟫ ≠ b j) :
    ∃ (a' : Fin (n + 1) → EuclideanSpace ℝ (Fin d)) (b' : Fin (n + 1) → ℝ),
      (∀ j : Fin n, a' j.castSucc = a j ∧ b' j.castSucc = b j) ∧
      Hpoly a' b' = Hpoly a b ∧
      a' (Fin.last n) ≠ 0 ∧
      ⟪a' (Fin.last n), v⟫ = b' (Fin.last n) ∧
      ⟪a' (Fin.last n), u⟫ < b' (Fin.last n) ∧
      (∀ x ∈ Hpoly a' b', ⟪a' (Fin.last n), x⟫ = b' (Fin.last n) ↔ x = v) ∧
      (∀ j, a' j ≠ 0 → ⟪a' j, u⟫ ≠ b' j ∨ ⟪a' j, v⟫ ≠ b' j) := by
  obtain ⟨c, β, hc, hcv, hcu, hle, heq⟩ :=
    exposing_row_from_active_sum d n a b u v hu hv huv
  let a' : Fin (n + 1) → EuclideanSpace ℝ (Fin d) := Fin.snoc a c
  let b' : Fin (n + 1) → ℝ := Fin.snoc b β
  have hrows : ∀ j : Fin n, a' j.castSucc = a j ∧ b' j.castSucc = b j := by
    intro j
    simp [a', b']
  have halast : a' (Fin.last n) = c := by simp [a']
  have hblast : b' (Fin.last n) = β := by simp [b']
  have hpoly : Hpoly a' b' = Hpoly a b := by
    ext x
    constructor
    · intro hx j
      have h := hx j.castSucc
      rw [(hrows j).1, (hrows j).2] at h
      exact h
    · intro hx j
      refine Fin.lastCases ?_ (fun k => ?_) j
      · rw [halast, hblast]
        exact hle x hx
      · rw [(hrows k).1, (hrows k).2]
        exact hx k
  refine ⟨a', b', hrows, hpoly, ?_, ?_, ?_, ?_, ?_⟩
  · rw [halast]
    exact hc
  · rw [halast, hblast]
    exact hcv
  · rw [halast, hblast]
    exact hcu
  · intro x hx
    rw [halast, hblast]
    exact heq x (hpoly ▸ hx)
  · intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · intro _
      left
      rw [halast, hblast]
      exact ne_of_lt hcu
    · intro haj
      have hak : a k ≠ 0 := by simpa only [(hrows k).1] using haj
      simpa only [(hrows k).1, (hrows k).2] using hsep k hak

#print axioms solution
