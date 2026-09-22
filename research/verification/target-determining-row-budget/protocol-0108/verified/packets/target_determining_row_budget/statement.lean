import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.target_determining_row_budget_routes (d m : ℕ) (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))={x | ∀ i, A i x ≤ b i})
    (u v : Fin d → ℝ)
    (hu : u ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (hv : v ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ) :
    let V := @Finset.filter (Fin d → ℝ)
      (fun x => x ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
      (fun _ => Classical.propDecidable _) C
    let T := @Finset.filter (Fin m) (fun i => A i v=b i ∧ A i u ≠ b i)
      (fun _ => Classical.propDecidable _) Finset.univ
    let G := @Finset.filter (Fin m) (fun i => A i u=b i ∧ A i v=b i)
      (fun _ => Classical.propDecidable _) Finset.univ
    ∃ S : Finset (Fin m), S ⊆ T ∧ S.card ≤ d ∧
      (∀ z : Fin d → ℝ, (∀ i ∈ G, A i z=0) → (∀ i ∈ S, A i z=0) → z=0) ∧
      ∃ L : ℕ, L ≤ ∑ i ∈ S, ((V.image (fun x => A i x)).card-1) ∧
        (∀ R : Finset (Fin m), R ⊆ T → R.card ≤ d →
          (∀ z : Fin d → ℝ, (∀ i ∈ G, A i z=0) → (∀ i ∈ R, A i z=0) → z=0) →
          (∑ i ∈ S, ((V.image (fun x => A i x)).card-1)) ≤
            ∑ i ∈ R, ((V.image (fun x => A i x)).card-1)) ∧
        (∀ K : ℕ, (∀ i ∈ S, (V.image (fun x => A i x)).card ≤ K+1) →
          L ≤ K*min d (m-d)) ∧
        ∃ p : Fin (L+1) → (Fin d → ℝ), p 0=u ∧ p (Fin.last L)=v ∧
          (∀ t, p t ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ) ∧
          ∀ t : Fin L, p t.castSucc ≠ p t.succ ∧
            IsExtreme ℝ {x : Fin d → ℝ | ∀ i, A i x ≤ b i}
              (segment ℝ (p t.castSucc) (p t.succ)) ∧
            (∀ i, A i v=b i → A i (p t.castSucc)=b i → A i (p t.succ)=b i) := by sorry
