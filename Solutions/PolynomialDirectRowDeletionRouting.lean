import Mathlib
import Solutions.PolynomialSingleCutLowerExcessRouting

open scoped RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace HirschDeletion

/-- Deleting row `j` from a `Fin (m+1)` H-presentation and then intersecting
with that row's halfspace recovers the original H-polyhedron exactly. -/
theorem hpoly_eq_deleteRow_inter_row
    {d m : ℕ}
    (a : Fin (m + 1) → EuclideanSpace ℝ (Fin d))
    (b : Fin (m + 1) → ℝ) (j : Fin (m + 1)) :
    Hpoly a b =
      Hpoly (fun k : Fin m => a (j.succAbove k))
        (fun k : Fin m => b (j.succAbove k)) ∩
      {z | ⟪a j, z⟫ ≤ b j} := by
  ext z
  constructor
  · intro hz
    refine ⟨?_, hz j⟩
    intro k
    exact hz (j.succAbove k)
  · rintro ⟨hout, hj⟩ i
    by_cases hij : i = j
    · subst i
      exact hj
    · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij
      subst i
      exact hout k

/-- If deleting one row leaves a bounded outer H-polyhedron, reinserting that
row is a genuine lower-row-excess clipping step.

The original presentation has `m+1` rows in dimension `d`; the deletion outer
has only `m` rows. Under `d ≤ m`, its row excess is strictly smaller than the
original `(m+1)-d`. A lower-excess induction hypothesis therefore pays the outer
cost `D`; the only additional charge is `B`, the intrinsic diameter of the
reinserted row's exposed face. -/
theorem hpoly_diamLE_of_bounded_deleteRow_outer
    {D B d m : ℕ}
    (hIH : HirschCircuitLocalization.LowerExcessHpolyDiameterBound
      ((m + 1) - d) D)
    (a : Fin (m + 1) → EuclideanSpace ℝ (Fin d))
    (b : Fin (m + 1) → ℝ)
    (hne : (Hpoly a b).Nonempty)
    (j : Fin (m + 1))
    (hdm : d ≤ m)
    (hbdOuter : Bornology.IsBounded
      (Hpoly (fun k : Fin m => a (j.succAbove k))
        (fun k : Fin m => b (j.succAbove k))))
    (hFace : DiamLE
      ((Hpoly a b) ∩ {z | ⟪a j, z⟫ = b j}) B) :
    DiamLE (Hpoly a b) (D + B) := by
  let ao : Fin m → EuclideanSpace ℝ (Fin d) :=
    fun k => a (j.succAbove k)
  let bo : Fin m → ℝ := fun k => b (j.succAbove k)
  have houterNonempty : (Hpoly ao bo).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    refine ⟨x, ?_⟩
    intro k
    exact hx (j.succAbove k)
  have hex : m - d < (m + 1) - d := by omega
  have hEq : Hpoly a b = Hpoly ao bo ∩ {z | ⟪a j, z⟫ ≤ b j} := by
    simpa [ao, bo] using hpoly_eq_deleteRow_inter_row a b j
  have hFace' : DiamLE
      (((Hpoly ao bo) ∩ {z | ⟪a j, z⟫ ≤ b j}) ∩
        {z | ⟪a j, z⟫ = b j}) B := by
    rw [← hEq]
    exact hFace
  have hroute :=
    HirschCircuitLocalization.hpoly_inter_halfspace_diamLE_of_lower_excess_outer
      hIH ao bo houterNonempty hbdOuter hex (a j) (b j) hFace'
  rw [← hEq] at hroute
  exact hroute

#print axioms hpoly_eq_deleteRow_inter_row
#print axioms hpoly_diamLE_of_bounded_deleteRow_outer

end HirschDeletion
