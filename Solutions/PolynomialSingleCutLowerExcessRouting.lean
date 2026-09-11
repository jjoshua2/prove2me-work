import Mathlib
import Solutions.PolynomialLowerExcessCarrierRecursion
import Solutions.PolynomialSimultaneousClipDiameter

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCircuitLocalization

/-- One-cut specialization of the public simultaneous-clipping geometry.
If a compact convex outer region has graph diameter `D`, and the exposed face
created by one added halfspace has intrinsic graph diameter `B`, the clipped
region has graph diameter at most `D+B`.

This isolates exactly the operation needed when an indispensable carrier row is
deleted and later reinserted. -/
theorem diamLE_inter_halfspace_of_compact_outer
    {d : ℕ}
    (Q : Set (EuclideanSpace ℝ (Fin d)))
    (hQc : IsCompact Q) (hQ : Convex ℝ Q)
    (c : EuclideanSpace ℝ (Fin d)) (beta : ℝ)
    (D B : ℕ) (hD : DiamLE Q D)
    (hFace : DiamLE
      ((Q ∩ {z | ⟪c, z⟫ ≤ beta}) ∩ {z | ⟪c, z⟫ = beta}) B) :
    DiamLE (Q ∩ {z | ⟪c, z⟫ ≤ beta}) (D + B) := by
  let aa : Fin 1 → EuclideanSpace ℝ (Fin d) := fun _ => c
  let bb : Fin 1 → ℝ := fun _ => beta
  let BB : Fin 1 → ℕ := fun _ => B
  have hFaces : ∀ i : Fin 1,
      DiamLE
        (HirschRadial.clipSet Q aa bb ∩ {z | ⟪aa i, z⟫ = bb i}) (BB i) := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa [HirschRadial.clipSet, aa, bb, BB] using hFace
  have h := HirschRadial.simultaneous_clipping_diameter_bound
    Q hQc hQ aa bb D BB hD hFaces
  simpa [HirschRadial.clipSet, aa, bb, BB] using h

/-- Recursive one-row reinsertion over a bounded lower-row-excess outer
H-polyhedron.

The outer H-polyhedron has strictly smaller row excess than `R`, so the supplied
induction hypothesis gives its ordinary graph cost `D`. Adding one new
inequality then costs only the intrinsic diameter `B` of the final exposed face.
This is the exact bounded-deletion branch suggested by an indispensable carrier
blocker. No claim is made that deleting a genuine row always leaves a bounded
outer H-polyhedron. -/
theorem hpoly_inter_halfspace_diamLE_of_lower_excess_outer
    {R D B d m : ℕ}
    (hIH : LowerExcessHpolyDiameterBound R D)
    (a : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ)
    (hne : (Hpoly a b).Nonempty)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hex : m - d < R)
    (c : EuclideanSpace ℝ (Fin d)) (beta : ℝ)
    (hFace : DiamLE
      (((Hpoly a b) ∩ {z | ⟪c, z⟫ ≤ beta}) ∩ {z | ⟪c, z⟫ = beta}) B) :
    DiamLE ((Hpoly a b) ∩ {z | ⟪c, z⟫ ≤ beta}) (D + B) := by
  have hD : DiamLE (Hpoly a b) D := hIH d m a b hne hbd hex
  have hclosed : IsClosed (Hpoly a b) := by
    rw [show Hpoly a b = ⋂ i : Fin m,
        {x : EuclideanSpace ℝ (Fin d) | ⟪a i, x⟫ ≤ b i} by
      ext x
      simp [Hpoly]]
    exact isClosed_iInter (fun i =>
      isClosed_le (continuous_const.inner continuous_id) continuous_const)
  have hcompact : IsCompact (Hpoly a b) :=
    Metric.isCompact_iff_isClosed_bounded.2 ⟨hclosed, hbd⟩
  have hconv : Convex ℝ (Hpoly a b) := by
    intro x hx y hy alpha beta' halpha hbeta hsum
    change ∀ i, ⟪a i, alpha • x + beta' • y⟫ ≤ b i
    intro i
    simp only [inner_add_right, inner_smul_right]
    have hx' := hx i
    have hy' := hy i
    have hxa := mul_le_mul_of_nonneg_left hx' halpha
    have hyb := mul_le_mul_of_nonneg_left hy' hbeta
    have hb : alpha * b i + beta' * b i = b i := by
      rw [← add_mul, hsum, one_mul]
    linarith
  exact diamLE_inter_halfspace_of_compact_outer
    (Hpoly a b) hcompact hconv c beta D B hD hFace

#print axioms diamLE_inter_halfspace_of_compact_outer
#print axioms hpoly_inter_halfspace_diamLE_of_lower_excess_outer

end HirschCircuitLocalization
