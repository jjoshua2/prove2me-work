import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.actual_planar_vertices_rank_attaining_original_routes (n : ℕ) (P : Set (Fin 2 → ℝ)) (v : Fin 2 → ℝ)
    (p : Fin (n+1) → (Fin 2 → ℝ))
    (h e : (Fin 2 → ℝ) →ₗ[ℝ] ℝ)
    (hP : P=convexHull ℝ ((insert v (Finset.univ.image p) : Finset (Fin 2 → ℝ)) : Set (Fin 2 → ℝ)))
    (hv : v ∈ P.extremePoints ℝ) (hp : ∀ i, p i ∈ P.extremePoints ℝ)
    (hpos : ∀ i, 0 < h (p i-v))
    (hinj : Function.Injective (fun z : Fin 2 → ℝ => (h z,e z)))
    (hw : StrictMono (fun i => e (p i-v)/h (p i-v))) :
    let w := fun i => e (p i-v)/h (p i-v)
    let a := fun i => 1/h (p i-v)
    let U := fun (t : ℝ) (k : Fin (n+1)) =>
      @Finset.filter ℝ (fun z => a k+t*w k < z) (fun _ => Classical.propDecidable _)
        (Finset.univ.image (fun i => a i+t*w i))
    let B := fun (t c : ℝ) (k : Fin (n+1)) =>
      @Finset.filter ℝ (fun z => z < 1/(a k+t*w k+c)) (fun _ => Classical.propDecidable _)
        (insert 0 (Finset.univ.image (fun i => 1/(a i+t*w i+c))))
    (∀ i j k : Fin (n+1), i < j → j < k →
      (a j-a i)*(w k-w j) < (a k-a j)*(w j-w i)) ∧
    (p 0 ≠ v ∧ IsExposed ℝ P (segment ℝ (p 0) v)) ∧
    (p (Fin.last n) ≠ v ∧ IsExposed ℝ P (segment ℝ (p (Fin.last n)) v)) ∧
    (∀ j : Fin n, p j.castSucc ≠ p j.succ ∧
      IsExposed ℝ P (segment ℝ (p j.castSucc) (p j.succ))) ∧
    ∃ M : ℝ, 0 < M ∧ ∀ k : Fin (n+1),
      (∀ t : ℝ, min k.val (n-k.val) ≤ (U t k).card) ∧
      (U (-M) k).card=k.val ∧ (U M k).card=n-k.val ∧
      ∃ L : ℕ, L=min k.val (n-k.val)+1 ∧ 2*L ≤ n+2 ∧
        (∀ t : ℝ, L ≤ (U t k).card+1) ∧
        (∃ t c : ℝ, (t=M ∨ t=-M) ∧ (∀ i, 0 < a i+t*w i+c) ∧ (B t c k).card=L) ∧
        ∃ q : Fin (L+1) → (Fin 2 → ℝ), q 0=p k ∧ q (Fin.last L)=v ∧
          (∀ i, q i ∈ P.extremePoints ℝ) ∧
          ∀ i : Fin L, q i.castSucc ≠ q i.succ ∧
            IsExposed ℝ P (segment ℝ (q i.castSucc) (q i.succ)) := by sorry
