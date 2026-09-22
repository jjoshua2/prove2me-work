import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.synthesized_face_normalizer_original_routes (d m : ℕ) (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))={x | ∀ i, A i x ≤ b i})
    (u v : Fin d → ℝ)
    (hu : u ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (hv : v ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ) :
    let V := @Finset.filter (Fin d → ℝ)
      (fun x => x ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
      (fun _ => Classical.propDecidable _) C
    let F := fun H : Finset (Fin m) => @Finset.filter (Fin d → ℝ)
      (fun x => ∀ i ∈ H, A i x=b i) (fun _ => Classical.propDecidable _) V
    let T := @Finset.filter (Fin m) (fun i => A i v=b i ∧ A i u ≠ b i)
      (fun _ => Classical.propDecidable _) Finset.univ
    let G := @Finset.filter (Fin m) (fun i => A i u=b i ∧ A i v=b i)
      (fun _ => Classical.propDecidable _) Finset.univ
    ∃ E : Finset (Fin m) → Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ,
      (∀ H, (∀ i ∈ H, A i v=b i) → ∀ j, ∀ x ∈ F H, 0<1+E H j (x-v)) ∧
      (∀ H, (∀ i ∈ H, A i v=b i) → ∀ j, ∀ a : ℝ, ∀ D : (Fin d → ℝ) →ₗ[ℝ] ℝ,
        (∀ x ∈ F H, 0<a+D x) →
          ((F H).image (fun x => (b j-A j x)/(1+E H j (x-v)))).card ≤
            ((F H).image (fun x => (b j-A j x)/(a+D x))).card) ∧
      let q : List (Fin m) → Finset (Fin m) → List ℕ :=
        List.rec (fun _ => []) (fun j _ tailCharges H =>
          (((F H).image (fun x => (b j-A j x)/(1+E H j (x-v)))).card-1) ::
            tailCharges (insert j H))
      ∃ J : List (Fin m), J.Nodup ∧ J.length ≤ min d (m-d) ∧
        (∀ i ∈ J, i ∈ T) ∧
        (∀ z : Fin d → ℝ, (∀ i ∈ G, A i z=0) → (∀ i ∈ J, A i z=0) → z=0) ∧
        ∃ L : ℕ, L ≤ (q J G).sum ∧
          (∀ R : List (Fin m), R.Nodup → R.length ≤ min d (m-d) →
            (∀ i ∈ R, i ∈ T) →
            (∀ z : Fin d → ℝ, (∀ i ∈ G, A i z=0) → (∀ i ∈ R, A i z=0) → z=0) →
            (q J G).sum ≤ (q R G).sum) ∧
          (∀ K : ℕ, (∀ k ∈ q J G, k ≤ K) → L ≤ K*min d (m-d)) ∧
          ∃ p : Fin (L+1) → (Fin d → ℝ), p 0=u ∧ p (Fin.last L)=v ∧
            (∀ t, p t ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ) ∧
            ∀ t : Fin L, p t.castSucc ≠ p t.succ ∧
              IsExtreme ℝ {x : Fin d → ℝ | ∀ i, A i x ≤ b i}
                (segment ℝ (p t.castSucc) (p t.succ)) ∧
              (∀ i, A i v=b i → A i (p t.castSucc)=b i → A i (p t.succ)=b i) := by sorry
