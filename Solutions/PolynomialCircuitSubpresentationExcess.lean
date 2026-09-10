import Mathlib
import Definitions.Def_Hirsch_common_face_geometry
import Solutions.PolynomialCommonFaceSubpresentationRank

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCircuitLocalization

open HirschPolynomialAccess

variable {d n : ℕ}

/-- Any ambient H-presentation possessing a vertex has at least as many rows as
its ambient dimension.  This is the row-count consequence of the already
proved vertex tight-row spanning lemma. -/
theorem rows_ge_dimension_of_vertex
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b)) :
    d ≤ n := by
  classical
  let U : Finset (Fin n) := Finset.univ
  let T := rowEvalMap a U
  have hTin : Function.Injective T := by
    intro p q hpq
    have hz : T (p - q) = 0 := by
      rw [map_sub, hpq, sub_self]
    have hz0 := vertex_tight_rows_span_checked
      d n a b u hu (p - q) ?_
    · exact sub_eq_zero.mp hz0
    · intro i _htight
      have hiU : i ∈ U := by simp [U]
      have hcoord := congrFun hz ⟨i, hiU⟩
      change ⟪a i, p - q⟫ = 0 at hcoord
      exact hcoord
  have hle := LinearMap.finrank_le_finrank_of_injective hTin
  have hdom : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
    finrank_euclideanSpace_fin (𝕜 := ℝ)
  have hcod : Module.finrank ℝ (U → ℝ) = n := by
    simp [U]
  rw [hdom, hcod] at hle
  exact hle

/-- Literal facet-excess-style form of the row-circuit defect budget for an
actual equivalent common-face subpresentation.

For any common-face subpresentation using at most `M` original rows, choose its
rows and discard those whose restricted coordinate normals vanish.  The
remaining effective set `F` still has at least `h = commonFaceDim` rows (because
zero is the coordinate image of the ambient vertex), and its excess over `h`
plus the loss of neutral rank is bounded by the ambient excess `n-d`:

`(F.card - h) + ((h - 1) - neutralRank(F)) ≤ n - d`.

This is the exact algebraic defect/excess inequality needed by the ordinary
Theorem-B argument.  What remains before replacing `F.card` by the geometric
number of common-face facets is only the semantic identification/selection of
one effective describing row per true facet. -/
theorem rowCircuit_commonFace_subpresentation_excess_defect
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u))
    (M : ℕ)
    (hsub : HirschCommonFace.CommonFaceHasSubpresentationAtMost a b u v M) :
    ∃ m : ℕ, m ≤ M ∧ ∃ e : Fin m ↪ Fin n,
      Hpoly
          (fun j => HirschCommonFace.commonFaceA a b u v (e j))
          (fun j => HirschCommonFace.commonFaceB a b u v (e j)) =
        Hpoly
          (HirschCommonFace.commonFaceA a b u v)
          (HirschCommonFace.commonFaceB a b u v) ∧
      let F : Finset (Fin n) :=
        (Finset.univ.map e) ∩ HirschCommonFace.commonFaceEffectiveRows a b u v
      HirschCommonFace.commonFaceDim a b u v ≤ F.card ∧
      F.card ≤ M ∧
      (F.card - HirschCommonFace.commonFaceDim a b u v) +
          ((HirschCommonFace.commonFaceDim a b u v - 1) -
            Module.finrank ℝ
              (((HirschCommonFace.rowEvalMap a
                (F ∩ Finset.univ.filter (fun i =>
                  a i ≠ 0 ∧ ⟪a i, v - u⟫ = 0))).domRestrict
                (HirschCommonFace.commonDirection a b u v)).range)) ≤
        n - d := by
  classical
  change HirschCommonFace.HasSubpresentationAtMost
    (HirschCommonFace.commonFaceA a b u v)
    (HirschCommonFace.commonFaceB a b u v) M at hsub
  obtain ⟨m, hm, e, he⟩ := hsub
  refine ⟨m, hm, e, he, ?_⟩
  let F : Finset (Fin n) :=
    (Finset.univ.map e) ∩ HirschCommonFace.commonFaceEffectiveRows a b u v
  have hlow : HirschCommonFace.commonFaceDim a b u v ≤ F.card := by
    simpa [F] using
      commonFace_subpresentation_effectiveRows_card_ge_dim
        a b u v hu m e he
  have hFcard : F.card ≤ M := by
    calc
      F.card ≤ (Finset.univ.map e).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = m := by simp
      _ ≤ M := hm
  have hFpub : F ⊆ HirschCommonFace.commonFaceEffectiveRows a b u v :=
    Finset.inter_subset_right
  have hFint :
      F ⊆ effectiveRowsOnSubspace a (commonDirection a b u v) := by
    rw [effectiveRowsOn_commonDirection_eq_publicCommonFaceEffectiveRows]
    exact hFpub
  have hdn : d ≤ n := rows_ge_dimension_of_vertex a b u hu
  have hexcess := rowCircuit_selectedEffectiveRows_excess_defect
    a b u v hu hcirc F hFint
    (by
      simpa [HirschCommonFace.commonFaceDim,
        HirschPolynomialAccess.commonFaceDim,
        HirschCommonFace.commonDirection, HirschCommonFace.commonSourceRows,
        HirschCommonFace.rowEvalMap,
        HirschPolynomialAccess.commonDirection,
        HirschPolynomialAccess.rowEvalMap,
        HirschPolynomialAccess.commonSourceRows] using hlow)
    hdn
  dsimp only
  refine ⟨hlow, hFcard, ?_⟩
  simpa [F, circuitNeutralRows,
    HirschCommonFace.commonFaceDim, HirschCommonFace.commonDirection,
    HirschCommonFace.rowEvalMap, HirschCommonFace.commonSourceRows,
    HirschPolynomialAccess.commonFaceDim, HirschPolynomialAccess.commonDirection,
    HirschPolynomialAccess.rowEvalMap, HirschPolynomialAccess.commonSourceRows] using hexcess

#print axioms rows_ge_dimension_of_vertex
#print axioms rowCircuit_commonFace_subpresentation_excess_defect

end HirschCircuitLocalization
