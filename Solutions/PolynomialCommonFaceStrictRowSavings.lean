import Mathlib
import Solutions.PolynomialCommonFaceRoutingModel
import Solutions.PolynomialCommonFaceIntrinsicRowCount

/-!
# Strict ambient rows buy intrinsic common-carrier excess savings

The used-face repair line needs more than a count of selected cut labels: it
needs a reason that many other used cuts make the recursive portal-pair carrier
strictly simpler.

This module proves the underlying resource inequality.  If `J` is a family of
original describing rows which is strictly slack at **every point** of the
common carrier of two parent vertices, then those rows cannot occur in an
equivalent strictly-feasible irredundant original-row presentation of that
carrier.  Combining this exclusion with the rows which vanish on the carrier
and rank-nullity gives

`(M_min - h) + |J| <= n - d`,

where `M_min` is the minimum equivalent original-row presentation count and `h`
is the intrinsic common-face dimension.

This is a row/excess resource theorem, not a diameter theorem.  In particular,
slackness only at the two endpoints is deliberately insufficient.
-/

open scoped BigOperators RealInnerProductSpace
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 6000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- An original row which is strictly slack everywhere on a common carrier
cannot be one of the rows of an equivalent strictly-feasible irredundant
original-row subpresentation.

The key point is the single-tight witness supplied by irredundancy: every
selected row has a feasible coordinate point where that row is tight.  Mapping
that point back to the ambient common face contradicts strict slackness. -/
theorem irredundant_commonFace_rows_disjoint_strict_rows
    {d n m : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (e : Fin m ↪ Fin n)
    (he :
      Hpoly
          (fun j => commonFaceA a b u v (e j))
          (fun j => commonFaceB a b u v (e j)) =
        Hpoly (commonFaceA a b u v) (commonFaceB a b u v))
    (hirr : RowPresentationIrredundant
      (fun j => commonFaceA a b u v (e j))
      (fun j => commonFaceB a b u v (e j)))
    (hstrict : StrictlyFeasibleRows
      (fun j => commonFaceA a b u v (e j))
      (fun j => commonFaceB a b u v (e j)))
    (J : Finset (Fin n))
    (hJ : ∀ i, i ∈ J → ∀ z ∈ commonFace a b u v, ⟪a i, z⟫ < b i) :
    Disjoint (Finset.univ.map e) J := by
  classical
  rw [Finset.disjoint_left]
  intro i hiF hiJ
  obtain ⟨k, _hk, rfl⟩ := Finset.mem_map.1 hiF
  obtain ⟨q, hqtight, hqother⟩ :=
    HirschRowCount.exists_single_tight_point_of_irredundant
      (fun j => commonFaceA a b u v (e j))
      (fun j => commonFaceB a b u v (e j)) hirr hstrict k
  have hqSel :
      q ∈ Hpoly
        (fun j => commonFaceA a b u v (e j))
        (fun j => commonFaceB a b u v (e j)) := by
    intro j
    by_cases hjk : j = k
    · subst j
      exact hqtight.le
    · exact (hqother j hjk).le
  have hqFull : q ∈ Hpoly (commonFaceA a b u v) (commonFaceB a b u v) := by
    rw [← he]
    exact hqSel
  have hqFace : commonFacePoint a b u v q ∈ commonFace a b u v :=
    (mem_commonFace_coord_iff a b u v q).1 hqFull
  have hlt := hJ (e k) hiJ (commonFacePoint a b u v q) hqFace
  have hrestricted := hqtight
  rw [commonFace_inner_restricted] at hrestricted
  dsimp [commonFaceB] at hrestricted
  have hambient : ⟪a (e k), commonFacePoint a b u v q⟫ = b (e k) := by
    dsimp [commonFacePoint]
    rw [inner_add_right]
    linarith
  linarith

/-- Main resource inequality.

For a bounded parent and two parent vertices, let `M_min` be the minimum number
of original common-face coordinate inequalities needed to describe their common
carrier, and let `h` be its intrinsic dimension.  Every collection `J` of
ambient rows which is strictly slack throughout that carrier buys one unit of
minimum-presentation excess saving:

`(M_min - h) + |J| <= n - d`.

No row-circuit hypothesis is used. -/
theorem commonFace_minExcess_add_strictRows_le
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (J : Finset (Fin n))
    (hJ : ∀ i, i ∈ J → ∀ z ∈ commonFace a b u v, ⟪a i, z⟫ < b i) :
    (commonFaceMinSubpresentationCount a b u v - commonFaceDim a b u v) +
        J.card ≤ n - d := by
  classical
  obtain ⟨m, _hmn, e, _q, he, _hbdSub, hirr, hstrict,
      h0ext, _hqext, _hpoint⟩ :=
    commonFace_edgeRefinement_ready_model a b u v hbd hu hv
  have hmin : commonFaceMinSubpresentationCount a b u v = m :=
    commonFace_minCount_eq_irredundant_subpresentation
      a b u v e he hirr hstrict
  let F : Finset (Fin n) := Finset.univ.map e
  let C : Finset (Fin n) := commonSourceRows a b u v
  have hFJ : Disjoint F J := by
    simpa [F] using
      irredundant_commonFace_rows_disjoint_strict_rows
        a b u v e he hirr hstrict J hJ
  have hnonzero : ∀ k : Fin m, commonFaceA a b u v (e k) ≠ 0 :=
    HirschCircuit.irredundant_rows_nonzero_of_mem
      (fun k => commonFaceA a b u v (e k))
      (fun k => commonFaceB a b u v (e k)) hirr 0 h0ext.1
  have hFC : Disjoint F C := by
    rw [Finset.disjoint_left]
    intro i hiF hiC
    obtain ⟨k, _hk, rfl⟩ := Finset.mem_map.1 hiF
    exact hnonzero k
      (commonFaceA_eq_zero_of_commonSourceRow a b u v (e k) hiC)
  have hJC : Disjoint J C := by
    rw [Finset.disjoint_left]
    intro i hiJ hiC
    have huFace : u ∈ commonFace a b u v := commonFace_u_mem a b u v hu.1
    have hlt := hJ i hiJ u huFace
    have heq : ⟪a i, u⟫ = b i := (Finset.mem_filter.1 hiC).2.2.1
    linarith
  have hdisj : Disjoint (F ∪ J) C :=
    Finset.disjoint_union_left.2 ⟨hFC, hJC⟩
  have htotal : F.card + J.card + C.card ≤ n := by
    have hsub : F ∪ J ∪ C ⊆ (Finset.univ : Finset (Fin n)) := by simp
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_union_of_disjoint hFJ] at hcard
    simpa using hcard
  let T := rowEvalMap a C
  have hnull := T.finrank_range_add_finrank_ker
  have hdom : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
    finrank_euclideanSpace_fin (𝕜 := ℝ)
  have hnull' :
      Module.finrank ℝ T.range + commonFaceDim a b u v = d := by
    rw [hdom] at hnull
    simpa [T, C, commonFaceDim, commonDirection] using hnull
  have hrange : Module.finrank ℝ T.range ≤ C.card := by
    calc
      Module.finrank ℝ T.range ≤ Module.finrank ℝ (C → ℝ) :=
        Submodule.finrank_le _
      _ = C.card := by simp [Fintype.card_coe]
  have hdim : d ≤ C.card + commonFaceDim a b u v := by omega
  have hface : commonFaceDim a b u v ≤ m :=
    rows_ge_dimension_of_vertex
      (fun k => commonFaceA a b u v (e k))
      (fun k => commonFaceB a b u v (e k)) 0 h0ext
  have hdn : d ≤ n := rows_ge_dimension_of_vertex a b u hu
  have hFcard : F.card = m := by simp [F]
  rw [hmin]
  omega

/-- If the rows strictly slack throughout a common carrier account for all but
at most `r` units of the ambient row excess, then the carrier's minimum
presentation excess is at most `r`.  This is the arithmetic form consumed by
small-excess routing. -/
theorem commonFace_minExcess_le_of_strictRows_card
    {d n r : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (J : Finset (Fin n))
    (hJ : ∀ i, i ∈ J → ∀ z ∈ commonFace a b u v, ⟪a i, z⟫ < b i)
    (hcard : n - d ≤ J.card + r) :
    commonFaceMinSubpresentationCount a b u v - commonFaceDim a b u v ≤ r := by
  have hsave := commonFace_minExcess_add_strictRows_le
    a b u v hbd hu hv J hJ
  omega

#print axioms irredundant_commonFace_rows_disjoint_strict_rows
#print axioms commonFace_minExcess_add_strictRows_le
#print axioms commonFace_minExcess_le_of_strictRows_card

end HirschCircuitLocalization
