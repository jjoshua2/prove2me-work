import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.finite_hull_original_coordinate_routes (d : ℕ) (C : Finset (Fin d → ℝ)) (u v : Fin d → ℝ)
    (hu : u ∈ (convexHull ℝ (C : Set (Fin d → ℝ))).extremePoints ℝ)
    (hv : v ∈ (convexHull ℝ (C : Set (Fin d → ℝ))).extremePoints ℝ) :
    let V := @Finset.filter (Fin d → ℝ)
      (fun x => x ∈ (convexHull ℝ (C : Set (Fin d → ℝ))).extremePoints ℝ)
      (fun p => Classical.propDecidable _) C
    ∃ L : ℕ, L ≤ ∑ j : Fin d, ((V.image (fun x => x j)).card-1) ∧
      ∃ p : Fin (L+1) → (Fin d → ℝ), p 0=u ∧ p (Fin.last L)=v ∧
        (∀ i, p i ∈ (convexHull ℝ (C : Set (Fin d → ℝ))).extremePoints ℝ) ∧
        ∀ i : Fin L, p i.castSucc ≠ p i.succ ∧
          IsExtreme ℝ (convexHull ℝ (C : Set (Fin d → ℝ)))
            (segment ℝ (p i.castSucc) (p i.succ)) := by sorry
