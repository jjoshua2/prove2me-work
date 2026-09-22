import Mathlib
set_option autoImplicit false

theorem Hirsch.affine_normalizer_finite_search (d : ℕ) (C : Finset (Fin d → ℝ))
    (s : (Fin d → ℝ) → ℝ) (u : Fin d → ℝ) (hu : u ∈ C) :
    let F := (C.product C).powerset.filter (fun B => B.card ≤ d)
    ∃ pick : F → ((Fin d → ℝ) →ₗ[ℝ] ℝ),
      (∀ B, ∀ x ∈ C, 0 < 1+pick B (x-u)) ∧
      (∀ B, (∃ D : (Fin d → ℝ) →ₗ[ℝ] ℝ,
        (∀ x ∈ C, 0 < 1+D (x-u)) ∧
          ∀ p ∈ B.val, D (s p.1 • (p.2-u)-s p.2 • (p.1-u))=s p.2-s p.1) →
        ∀ p ∈ B.val, pick B (s p.1 • (p.2-u)-s p.2 • (p.1-u))=s p.2-s p.1) ∧
      (∀ a : ℝ, ∀ D : (Fin d → ℝ) →ₗ[ℝ] ℝ,
        (∀ x ∈ C, 0 < a+D x) → ∃ B : F,
          (∀ x ∈ C, ∀ y ∈ C, s x/(a+D x)=s y/(a+D y) →
            s x/(1+pick B (x-u))=s y/(1+pick B (y-u))) ∧
          (C.image (fun x => s x/(1+pick B (x-u)))).card ≤
            (C.image (fun x => s x/(a+D x))).card) ∧
      ∃ B : F, ∀ a : ℝ, ∀ D : (Fin d → ℝ) →ₗ[ℝ] ℝ,
        (∀ x ∈ C, 0 < a+D x) →
          (C.image (fun x => s x/(1+pick B (x-u)))).card ≤
            (C.image (fun x => s x/(a+D x))).card := by sorry
