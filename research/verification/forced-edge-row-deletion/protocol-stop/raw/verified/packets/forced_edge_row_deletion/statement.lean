import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.forced_original_edges_survive_row_deletion (d m N : ℕ)
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (v : Fin d → ℝ)
    (hv : v ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (J : Finset (Fin m)) (u w : Fin N → (Fin d → ℝ))
    (hu : ∀ t, u t ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)))
    (hw : ∀ t, w t ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)))
    (huv : ∀ t, u t ≠ v) (hwv : ∀ t, w t ≠ v) (huw : ∀ t, u t ≠ w t)
    (hE : ∀ t, IsExposed ℝ {x : Fin d → ℝ | ∀ i, A i x ≤ b i}
      (segment ℝ (u t) (w t)))
    (hforced : ∀ t i, A i v < b i → A i (u t) = b i →
      A i (w t) = b i → i ∈ J) :
    let P : Set (Fin d → ℝ) := {x | ∀ i, A i x ≤ b i}
    let Q : Set (Fin d → ℝ) := {x | ∀ i, A i v = b i ∨ i ∈ J → A i x ≤ b i}
    let E := fun t : Fin N => {x ∈ Q | ∃ s : ℝ, x = u t + s • (w t - u t)}
    (∀ t, IsExposed ℝ Q (E t) ∧ P ∩ E t = segment ℝ (u t) (w t) ∧
      segment ℝ (u t) (w t) ⊆ E t ∧ v ∉ E t ∧
      Function.Injective (fun s : ℝ => u t + s • (w t - u t))) ∧
    (∀ s t, E s = E t → segment ℝ (u s) (w s) = segment ℝ (u t) (w t)) ∧
    (Function.Injective (fun t => segment ℝ (u t) (w t)) → Function.Injective E) := by sorry
