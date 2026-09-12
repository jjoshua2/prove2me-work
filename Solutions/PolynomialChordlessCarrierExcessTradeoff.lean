import Mathlib
import Solutions.PolynomialChordlessSupportCount
import Solutions.PolynomialDisjointCutCarrierSavings

/-!
# Chordless used support forces local carrier excess savings

This module composes the three verified ingredients of the current Polynomial
Hirsch target-cone line:

* shortest-region routing supplies a chordless parent-vertex face path;
* chordless support counting gives at least `r-3` selected labels which are
  nonneighbors of any fixed selected label;
* nonadjacent closed extreme faces are disjoint, so when selected labels are
  actual row faces those `r-3` rows are strictly slack throughout the current
  portal-pair carrier; PR #186 then converts them to presentation-excess saving.

The resulting theorem is the intended support-versus-subproblem-size tradeoff:

`local carrier minimum-presentation excess + (r - 3) <= n - d`.

No recursive diameter hypothesis occurs in the statement.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 6000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess HirschRegionRoute

/-- On a chordless parent-vertex face path, suppose a selected set `cuts` of
path labels is injectively identified with original H-presentation rows and each
selected face is exactly the corresponding row face.  Fix one selected label
`i` and two parent vertices `p,q` tight on its row.

At most three selected labels are blocked from being useful strict rows: `i`
itself and at most its predecessor/successor.  Every other selected label is
nonadjacent to `i`, hence its row face is disjoint from the current row face and
its row is strict throughout `commonFace p q`.  Consequently

`(M_min(p,q) - h(p,q)) + (cuts.card - 3) <= n-d`. -/
theorem commonFace_minExcess_add_selected_sub_three_le_of_chordless_rowFaces
    {d n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact (Hpoly a b))
    (hF : ∀ k, IsExtreme ℝ (Hpoly a b) (F k))
    (hclosed : ∀ k, IsClosed (F k))
    (row : ι → Fin n)
    {s t : ι}
    (path :
      (intersectionGraph (fun k => extremePoints ℝ (Hpoly a b) ∩ F k)).Walk s t)
    (hchord : WalkChordless path)
    (cuts : Finset ι) (hcuts : cuts ⊆ path.support.toFinset)
    (hrowinj : Set.InjOn row (↑cuts : Set ι))
    (hface : ∀ k, k ∈ cuts → F k = hpolyRowFace a b (row k))
    (i : ι) (hi : i ∈ cuts)
    (p q : EuclideanSpace ℝ (Fin d))
    (hp : p ∈ extremePoints ℝ (Hpoly a b))
    (hq : q ∈ extremePoints ℝ (Hpoly a b))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hai : a (row i) ≠ 0)
    (hpi : ⟪a (row i), p⟫ = b (row i))
    (hqi : ⟪a (row i), q⟫ = b (row i)) :
    (commonFaceMinSubpresentationCount a b p q - commonFaceDim a b p q) +
        (cuts.card - 3) ≤ n - d := by
  classical
  let S : Finset ι := nonneighborSelectedFinset path cuts i
  let J : Finset (Fin n) := S.image row
  have hScuts : S ⊆ cuts := by
    intro k hk
    exact (mem_nonneighborSelectedFinset path cuts hcuts i k hk).1
  have hSinj : Set.InjOn row (↑S : Set ι) := by
    intro x hx y hy hxy
    exact hrowinj (hScuts hx) (hScuts hy) hxy
  have hJcard : J.card = S.card := by
    exact Finset.card_image_iff.mpr hSinj
  have hSbig : cuts.card - 3 ≤ S.card := by
    exact nonneighborSelectedFinset_card_ge_sub_three
      path hchord cuts hcuts i hi
  have hJdisj : ∀ j, j ∈ J →
      Disjoint (hpolyRowFace a b (row i)) (hpolyRowFace a b j) := by
    intro j hj
    obtain ⟨k, hkS, hrow⟩ := Finset.mem_image.mp hj
    have hkInfo := mem_nonneighborSelectedFinset path cuts hcuts i k hkS
    have hkcut : k ∈ cuts := hkInfo.1
    have hki : i ≠ k := hkInfo.2.1.symm
    have hnadj := hkInfo.2.2
    have hdisjF : Disjoint (F i) (F k) :=
      closed_extreme_faces_disjoint_of_region_nonadj
        (Hpoly a b) F hP hF hclosed hki hnadj
    rw [hface i hi, hface k hkcut] at hdisjF
    simpa [hrow] using hdisjF
  have hsave := commonFace_minExcess_add_disjoint_rowFaces_le
    a b p q hp hq hbd (row i) hai hpi hqi J hJdisj
  rw [hJcard] at hsave
  omega

/-- Arithmetic corollary: a selected support of size `r` forces the current
portal-pair carrier's minimum-presentation excess to be at most
`(n-d) - (r-3)` in the nontruncated inequality form `local + (r-3) <= n-d`.
In particular, if `cuts.card = n-d`, then the local excess is at most three. -/
theorem commonFace_minExcess_le_three_of_chordless_maximal_rowFace_support
    {d n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact (Hpoly a b))
    (hF : ∀ k, IsExtreme ℝ (Hpoly a b) (F k))
    (hclosed : ∀ k, IsClosed (F k))
    (row : ι → Fin n)
    {s t : ι}
    (path :
      (intersectionGraph (fun k => extremePoints ℝ (Hpoly a b) ∩ F k)).Walk s t)
    (hchord : WalkChordless path)
    (cuts : Finset ι) (hcuts : cuts ⊆ path.support.toFinset)
    (hrowinj : Set.InjOn row (↑cuts : Set ι))
    (hface : ∀ k, k ∈ cuts → F k = hpolyRowFace a b (row k))
    (hmax : cuts.card = n - d)
    (i : ι) (hi : i ∈ cuts)
    (p q : EuclideanSpace ℝ (Fin d))
    (hp : p ∈ extremePoints ℝ (Hpoly a b))
    (hq : q ∈ extremePoints ℝ (Hpoly a b))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hai : a (row i) ≠ 0)
    (hpi : ⟪a (row i), p⟫ = b (row i))
    (hqi : ⟪a (row i), q⟫ = b (row i)) :
    commonFaceMinSubpresentationCount a b p q - commonFaceDim a b p q ≤ 3 := by
  have htrade :=
    commonFace_minExcess_add_selected_sub_three_le_of_chordless_rowFaces
      a b F hP hF hclosed row path hchord cuts hcuts hrowinj hface
      i hi p q hp hq hbd hai hpi hqi
  rw [hmax] at htrade
  omega

#print axioms commonFace_minExcess_add_selected_sub_three_le_of_chordless_rowFaces
#print axioms commonFace_minExcess_le_three_of_chordless_maximal_rowFace_support

end HirschCircuitLocalization
