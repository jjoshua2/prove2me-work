import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.strict_convex_chain_exact_source_rank (n : ℕ) (w a : Fin (n+1) → ℝ)
    (hw : StrictMono w)
    (ha : ∀ i j k : Fin (n+1), i<j → j<k →
      (a j-a i)*(w k-w j) < (a k-a j)*(w j-w i)) :
    let U := fun (t : ℝ) (k : Fin (n+1)) =>
      @Finset.filter ℝ (fun z => a k+t*w k<z) (fun _ => Classical.propDecidable _)
        (Finset.univ.image (fun i => a i+t*w i))
    let B := fun (t c : ℝ) (k : Fin (n+1)) =>
      @Finset.filter ℝ (fun z => z<1/(a k+t*w k+c)) (fun _ => Classical.propDecidable _)
        (insert 0 (Finset.univ.image (fun i => 1/(a i+t*w i+c))))
    ∃ M : ℝ, 0<M ∧ ∀ k : Fin (n+1),
      (∀ t : ℝ, min k.val (n-k.val) ≤ (U t k).card) ∧
      (U (-M) k).card=k.val ∧ (U M k).card=n-k.val ∧
      ∃ t c : ℝ, (t=M ∨ t=-M) ∧ (∀ i, 0<a i+t*w i+c) ∧
        (U t k).card=min k.val (n-k.val) ∧
        (B t c k).card=min k.val (n-k.val)+1 ∧
        2*(B t c k).card ≤ n+2 := by sorry
