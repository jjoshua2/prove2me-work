import Mathlib
import Solutions.PolynomialFaceReentrySplice
import Solutions.PolynomialLowExcessSectionDescent

open scoped RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace HirschFaceSplice

/-- Reentry splicing only needs a bounded parent-edge route between the two
selected visits.  It does not actually require an intrinsic `DiamLE` theorem
for the face or that the replacement walk remain inside the face.

This is the form needed by the already-Proved facet-reduction theorem, whose
conclusion is an ambient parent-edge walk between two vertices on a facet. -/
theorem splice_reentry_through_parent_route
    (d L B s t : ℕ)
    (P F : Set (EuclideanSpace ℝ (Fin d)))
    (hroute : ∀ x,
      x ∈ extremePoints ℝ P → x ∈ F →
      ∀ y, y ∈ extremePoints ℝ P → y ∈ F →
      ∃ wf : ℕ → EuclideanSpace ℝ (Fin d),
        wf 0 = x ∧ wf B = y ∧
        ∀ j < B, wf j = wf (j + 1) ∨ Adj P (wf j) (wf (j + 1)))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hwstep : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hst : s ≤ t) (htL : t ≤ L)
    (hsP : w s ∈ extremePoints ℝ P)
    (htP : w t ∈ extremePoints ℝ P)
    (hsF : w s ∈ F) (htF : w t ∈ F) :
    ∃ w' : ℕ → EuclideanSpace ℝ (Fin d),
      w' 0 = u ∧ w' (s + B + (L - t)) = v ∧
      ∀ j < s + B + (L - t),
        w' j = w' (j + 1) ∨ Adj P (w' j) (w' (j + 1)) := by
  have hsL : s ≤ L := hst.trans htL
  obtain ⟨wf, hwf0, hwfB, hwfstep⟩ :=
    hroute (w s) hsP hsF (w t) htP htF

  let wp : ℕ → EuclideanSpace ℝ (Fin d) := fun j => w j
  have hwp0 : wp 0 = u := by simpa [wp] using hw0
  have hwps : wp s = w s := rfl
  have hwpstep : ∀ j < s,
      wp j = wp (j + 1) ∨ Adj P (wp j) (wp (j + 1)) := by
    intro j hj
    simpa [wp] using hwstep j (lt_of_lt_of_le hj hsL)

  let ws : ℕ → EuclideanSpace ℝ (Fin d) := fun j => w (t + j)
  have hws0 : ws 0 = w t := by simp [ws]
  have hwsB : ws (L - t) = v := by
    have hidx : t + (L - t) = L := by omega
    simpa [ws, hidx] using hwL
  have hwsstep : ∀ j < L - t,
      ws j = ws (j + 1) ∨ Adj P (ws j) (ws (j + 1)) := by
    intro j hj
    have hidx : t + j < L := by omega
    have h := hwstep (t + j) hidx
    simpa [ws, Nat.add_assoc] using h

  obtain ⟨wpf, hwpf0, hwpfB, hwpfstep⟩ :=
    HirschProduct.append_walk (Adj P) wp wf
      hwp0 hwps hwf0 hwfB hwpstep hwfstep
  obtain ⟨w', hw'0, hw'B, hw'step⟩ :=
    HirschProduct.append_walk (Adj P) wpf ws
      hwpf0 hwpfB hws0 hwsB hwpfstep hwsstep
  refine ⟨w', hw'0, ?_, ?_⟩
  · simpa [Nat.add_assoc] using hw'B
  · simpa [Nat.add_assoc] using hw'step

/-- A dimension-lower uniform H-polytope bound, together with the already-Proved
facet-reduction input, gives an ambient parent-edge route of the same budget
between any two parent vertices lying on a selected nonzero-row facet.

For a presentation with `k+1` rows in dimension `d`, the recursive premise is
on `k` rows in dimension `d-1`, so row excess is preserved exactly. -/
theorem hpoly_facet_parent_route_of_lower_dimension_bound
    (hfacet : HirschLowExcess.FacetWalkReduction)
    {d k B : ℕ}
    (a : Fin (k + 1) → EuclideanSpace ℝ (Fin d))
    (b : Fin (k + 1) → ℝ)
    (i : Fin (k + 1)) (hai : a i ≠ 0)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hlow : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1)))
      (b' : Fin k → ℝ),
      Bornology.IsBounded (Hpoly a' b') → DiamLE (Hpoly a' b') B)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hui : ⟪a i, u⟫ = b i) (hvi : ⟪a i, v⟫ = b i) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
      w 0 = u ∧ w B = v ∧
      ∀ j < B, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  have huF : u ∈ extremePoints ℝ
      {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i} := by
    refine ⟨⟨hu.1, hui⟩, ?_⟩
    intro x hx y hy hseg
    exact hu.2 hx.1 hy.1 hseg
  have hvF : v ∈ extremePoints ℝ
      {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i} := by
    refine ⟨⟨hv.1, hvi⟩, ?_⟩
    intro x hx y hy hseg
    exact hv.2 hx.1 hy.1 hseg
  exact hfacet d k a b i hai hbd B hlow u v huF hvF

/-- Repeated visits to one selected H-polytope facet can therefore be compressed
to one same-excess, lower-dimensional recursion charge.

The original path may leave and re-enter the facet arbitrarily many times
between `s` and `t`; the repaired path pays only the one lower-dimensional
budget `B` for the entire interval. -/
theorem splice_reentry_through_hpoly_facet_of_lower_dimension_bound
    (hfacet : HirschLowExcess.FacetWalkReduction)
    {d k L B s t : ℕ}
    (a : Fin (k + 1) → EuclideanSpace ℝ (Fin d))
    (b : Fin (k + 1) → ℝ)
    (i : Fin (k + 1)) (hai : a i ≠ 0)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hlow : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1)))
      (b' : Fin k → ℝ),
      Bornology.IsBounded (Hpoly a' b') → DiamLE (Hpoly a' b') B)
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hwstep : ∀ j < L,
      w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)))
    (hst : s ≤ t) (htL : t ≤ L)
    (hsP : w s ∈ extremePoints ℝ (Hpoly a b))
    (htP : w t ∈ extremePoints ℝ (Hpoly a b))
    (hsF : ⟪a i, w s⟫ = b i)
    (htF : ⟪a i, w t⟫ = b i) :
    ∃ w' : ℕ → EuclideanSpace ℝ (Fin d),
      w' 0 = u ∧ w' (s + B + (L - t)) = v ∧
      ∀ j < s + B + (L - t),
        w' j = w' (j + 1) ∨ Adj (Hpoly a b) (w' j) (w' (j + 1)) := by
  let F : Set (EuclideanSpace ℝ (Fin d)) :=
    {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i}
  have hroute : ∀ x,
      x ∈ extremePoints ℝ (Hpoly a b) → x ∈ F →
      ∀ y, y ∈ extremePoints ℝ (Hpoly a b) → y ∈ F →
      ∃ wf : ℕ → EuclideanSpace ℝ (Fin d),
        wf 0 = x ∧ wf B = y ∧
        ∀ j < B, wf j = wf (j + 1) ∨
          Adj (Hpoly a b) (wf j) (wf (j + 1)) := by
    intro x hxP hxF y hyP hyF
    exact hpoly_facet_parent_route_of_lower_dimension_bound
      hfacet a b i hai hbd hlow x y hxP hyP hxF.2 hyF.2
  exact splice_reentry_through_parent_route d L B s t (Hpoly a b) F
    hroute u v w hw0 hwL hwstep hst htL hsP htP
    ⟨hsP.1, hsF⟩ ⟨htP.1, htF⟩

#print axioms splice_reentry_through_parent_route
#print axioms hpoly_facet_parent_route_of_lower_dimension_bound
#print axioms splice_reentry_through_hpoly_facet_of_lower_dimension_bound

end HirschFaceSplice
