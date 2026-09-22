import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.source_rank_reoptimized_original_routes (d m : ℕ) (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))={x | ∀ i, A i x ≤ b i})
    (u v : Fin d → ℝ)
    (hu : u ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (hv : v ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ) :
    let V := @Finset.filter (Fin d → ℝ)
      (fun x => x ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
      (fun _ => Classical.propDecidable _) C
    let F := fun x : Fin d → ℝ => @Finset.filter (Fin d → ℝ)
      (fun z => ∀ i, A i v=b i → A i x=b i → A i z=b i)
      (fun _ => Classical.propDecidable _) V
    ∃ h : (Fin d → ℝ) →ₗ[ℝ] ℝ, (∀ z ∈ C, z ≠ v → 0<h (z-v)) ∧
      ∃ E : (Fin d → ℝ) → (Fin d → ℝ) →ₗ[ℝ] ℝ,
        (∀ x ∈ V, ∀ z ∈ F x, 0<1+E x (z-v)) ∧
        let R := fun (x : Fin d → ℝ) (D : (Fin d → ℝ) →ₗ[ℝ] ℝ) =>
          @Finset.filter ℝ (fun a => a<h (x-v)/(1+D (x-v)))
            (fun _ => Classical.propDecidable _)
            ((F x).image (fun z => h (z-v)/(1+D (z-v))))
        (∀ x ∈ V, ∀ D : (Fin d → ℝ) →ₗ[ℝ] ℝ,
          (∀ z ∈ F x, 0<1+D (z-v)) → (R x (E x)).card ≤ (R x D).card) ∧
        (R v (E v)).card=0 ∧
        ∃ L : ℕ, L ≤ (R u (E u)).card ∧
          (∀ D : (Fin d → ℝ) →ₗ[ℝ] ℝ,
            (∀ z ∈ F u, 0<1+D (z-v)) → L ≤ (R u D).card) ∧
          ∃ p : Fin (L+1) → (Fin d → ℝ), p 0=u ∧ p (Fin.last L)=v ∧
            (∀ t, p t ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ) ∧
            ∀ t : Fin L,
              (p t.castSucc ≠ p t.succ ∧
                IsExtreme ℝ {x : Fin d → ℝ | ∀ i, A i x ≤ b i}
                  (segment ℝ (p t.castSucc) (p t.succ)) ∧
                (∀ i, A i v=b i → A i (p t.castSucc)=b i → A i (p t.succ)=b i)) ∧
              (R (p t.succ) (E (p t.succ))).card <
                (R (p t.castSucc) (E (p t.castSucc))).card := by sorry
