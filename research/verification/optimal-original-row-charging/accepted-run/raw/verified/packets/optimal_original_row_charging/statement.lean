import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.optimal_original_row_edge_charging (d m N : ℕ)
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (v : Fin d → ℝ)
    (hv : v ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (u w : Fin N → (Fin d → ℝ))
    (hu : ∀ t, u t ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (hw : ∀ t, w t ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (huv : ∀ t, u t ≠ v) (hwv : ∀ t, w t ≠ v) (huw : ∀ t, u t ≠ w t)
    (hE : ∀ t, IsExposed ℝ {x : Fin d → ℝ | ∀ i, A i x ≤ b i}
      (segment ℝ (u t) (w t))) :
    let I := @Finset.filter (Fin m) (fun i => A i v < b i)
      (fun _ => Classical.propDecidable _) Finset.univ
    let S := fun t : Fin N => @Finset.filter (Fin m)
      (fun i => A i v < b i ∧ A i (u t) = b i ∧ A i (w t) = b i)
      (fun _ => Classical.propDecidable _) Finset.univ
    let F := fun J : Finset (Fin m) => @Finset.filter (Fin N) (fun t => S t ⊆ J)
      (fun _ => Classical.propDecidable _) Finset.univ
    let Cap := fun k : ℕ => ∃ f : Fin N → Fin m, (∀ t, f t ∈ S t) ∧
      ∀ i : Fin m, (@Finset.filter (Fin N) (fun t => f t = i)
        (fun _ => Classical.propDecidable _) Finset.univ).card ≤ k
    ∃ K : ℕ, K ≤ N ∧ N ≤ K * I.card ∧ Cap K ∧
      (∀ k : ℕ, Cap k ↔ K ≤ k) ∧
      (∀ k : ℕ, Cap k ↔ ∀ J ⊆ I, (F J).card ≤ k * J.card) ∧
      (∀ k : ℕ, k < K → ∃ J : Finset (Fin m), J ⊆ I ∧ J.Nonempty ∧
        k * J.card < (F J).card ∧ (F J).card ≤ K * J.card) := by sorry
