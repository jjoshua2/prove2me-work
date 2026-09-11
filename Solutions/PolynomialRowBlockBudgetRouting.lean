import Mathlib
import Solutions.PolynomialRowBlockRouting

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace HirschRowBlocks

/-- Generic additive routing for an algebraic row-block decomposition.

Unlike `hpoly_diamLE_excess_of_small_row_blocks`, this theorem assumes an
arbitrary proved diameter budget `B i` for each factor and simply transports
the product walk back to the original H-polyhedron. No boundedness,
nonemptiness, row-count, or small-excess hypothesis is needed by the transport
itself.

This is the recursive interface: any independently proved factor bounds add,
rather than multiply. -/
theorem hpoly_diamLE_sum_of_row_block_bounds
    {d n k : ℕ} (dims counts : Fin k → ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ]
      (∀ i : Fin k, EuclideanSpace ℝ (Fin (dims i))))
    (e : (Σ i : Fin k, Fin (counts i)) ≃ Fin n)
    (A : ∀ i : Fin k, Fin (counts i) → EuclideanSpace ℝ (Fin (dims i)))
    (hrows : ∀ z i j, ⟪a (e ⟨i, j⟩), T.symm z⟫ = ⟪A i j, z i⟫)
    (B : Fin k → ℕ)
    (hD : ∀ i, DiamLE (Hpoly (A i) (fun j => b (e ⟨i, j⟩))) (B i)) :
    DiamLE (Hpoly a b) (∑ i, B i) := by
  have hprod := HirschProduct.diamLE_pi
    (fun i => Hpoly (A i) (fun j => b (e ⟨i, j⟩))) B hD
  rw [← image_hpoly_eq_pi_of_row_blocks dims counts a b T e A hrows] at hprod
  exact
    (Hirsch.affineEquiv_diamLE_image_iff
      T.toAffineEquiv (Hpoly a b) (∑ i, B i)).mp hprod

#print axioms hpoly_diamLE_sum_of_row_block_bounds

end HirschRowBlocks
