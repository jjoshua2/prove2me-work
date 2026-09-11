import Mathlib
import Solutions.PolynomialExcessTwoPairVertices

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 3000000
set_option autoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschExcessTwo

/-- The face obtained by requiring all coordinates outside `S` to vanish. -/
def supportFace {n : ℕ} (t : Fin n → ℝ) (mu : ℝ) (S : Finset (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {s | s ∈ momentSlice t mu ∧ ∀ k, k ∉ S → s k = 0}

lemma supportFace_subset {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (S : Finset (Fin n)) :
    supportFace t mu S ⊆ momentSlice t mu := by
  intro s hs
  exact hs.1

/-- Coordinate support carriers are extreme faces. This packages simultaneous
preservation of all common zero coordinates into one face. -/
theorem supportFace_isExtreme {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (S : Finset (Fin n)) :
    IsExtreme ℝ (momentSlice t mu) (supportFace t mu S) := by
  refine ⟨supportFace_subset t mu S, ?_⟩
  intro x hx y hy z hz hseg
  refine ⟨hx, ?_⟩
  intro k hk
  have hz0 : z ∈ zeroFace t mu k := ⟨hz.1, hz.2 k hk⟩
  have hx0 := (zeroFace_isExtreme t mu k).left_mem_of_mem_openSegment hx hy hz0 hseg
  exact hx0.2

/-- A low/high pair vertex belongs to every support carrier containing its two
indices. -/
lemma pairPoint_mem_supportFace {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j : Fin n)
    (hli : t i < mu) (hrj : mu < t j)
    (S : Finset (Fin n)) (hiS : i ∈ S) (hjS : j ∈ S) :
    pairPoint t mu i j ∈ supportFace t mu S := by
  classical
  have hij : i ≠ j := by
    intro h
    subst j
    linarith
  refine ⟨pairPoint_mem t mu i j hli hrj, ?_⟩
  intro k hk
  have hki : k ≠ i := by
    intro h
    subst k
    exact hk hiS
  have hkj : k ≠ j := by
    intro h
    subst k
    exact hk hjS
  exact pairPoint_apply_other t mu i j k hki hkj

#print axioms supportFace_isExtreme
#print axioms pairPoint_mem_supportFace

end HirschExcessTwo
