import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.inverse_affine_source_rank_reduction (d : ℕ) (C S : Finset (Fin d → ℝ))
    (h : (Fin d → ℝ) →ₗ[ℝ] ℝ) (v x : Fin d → ℝ)
    (hSC : S ⊆ C) (hv : v ∈ S) (hx : x ∈ S) (hxv : x ≠ v)
    (hh : ∀ z ∈ C, z ≠ v → 0<h (z-v)) :
    let U := fun D : (Fin d → ℝ) →ₗ[ℝ] ℝ =>
      @Finset.filter ℝ (fun a => (1+D (x-v))/h (x-v)<a)
        (fun _ => Classical.propDecidable _)
        ((S.erase v).image (fun z => (1+D (z-v))/h (z-v)))
    let R := fun D : (Fin d → ℝ) →ₗ[ℝ] ℝ =>
      @Finset.filter ℝ (fun a => a<h (x-v)/(1+D (x-v)))
        (fun _ => Classical.propDecidable _)
        (S.image (fun z => h (z-v)/(1+D (z-v))))
    (∀ D : (Fin d → ℝ) →ₗ[ℝ] ℝ, ∃ c : ℝ,
      (∀ z ∈ C, 0<1+(D+c • h) (z-v)) ∧ (U (D+c • h)).card=(U D).card) ∧
    (∀ D : (Fin d → ℝ) →ₗ[ℝ] ℝ, (∀ z ∈ S, 0<1+D (z-v)) →
      (R D).card=(U D).card+1) ∧
    (∀ z ∈ C, z ≠ v → ∀ w ∈ C, w ≠ v →
      h ((h (z-v))⁻¹ • (z-v)-(h (w-v))⁻¹ • (w-v))=0) ∧
    ∃ D : (Fin d → ℝ) →ₗ[ℝ] ℝ,
      (∀ z ∈ C, 0<1+D (z-v)) ∧ (R D).card=(U D).card+1 ∧
      (∀ E : (Fin d → ℝ) →ₗ[ℝ] ℝ, (U D).card ≤ (U E).card) ∧
      (∀ E : (Fin d → ℝ) →ₗ[ℝ] ℝ, (∀ z ∈ S, 0<1+E (z-v)) →
        (R D).card ≤ (R E).card) := by sorry
