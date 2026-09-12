import Mathlib
import Definitions.Def_Hirsch_model
open Set Hirsch
open scoped BigOperators RealInnerProductSpace
theorem Hirsch.vertex_has_injective_target_tight_basis {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    ∃ e : Fin d ↪ Fin n,
      Function.Injective (fun x : EuclideanSpace ℝ (Fin d) => fun k : Fin d => ⟪a (e k), x⟫) ∧
      ∀ k, ⟪a (e k), v⟫ = b (e k) := by sorry
