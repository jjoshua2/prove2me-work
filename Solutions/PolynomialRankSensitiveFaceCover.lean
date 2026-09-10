import Mathlib
import Solutions.PolynomialBalancedRowFaceCover
import Solutions.PolynomialWeightedFaceCover

open scoped BigOperators RealInnerProductSpace
open Set Hirsch
set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschRankFaceCover

/-- Tight rows outside any normal subspace U supply at least codim U
independent constraints in aggregate. No simplicity or irredundancy is needed. -/
theorem tight_rows_outside_subspace_card_ge_codim
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    d - Module.finrank ℝ U ≤
      (Finset.univ.filter (fun i => a i ∉ U ∧ ⟪a i, x⟫ = b i)).card := by
  classical
  let S : Finset (Fin n) :=
    Finset.univ.filter (fun i => a i ∉ U ∧ ⟪a i, x⟫ = b i)
  let T : Uᗮ →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun y i => ⟪a i.1, (y : EuclideanSpace ℝ (Fin d))⟫
      map_add' := by
        intro y z
        funext i
        simp [inner_add_right]
      map_smul' := by
        intro c y
        funext i
        simp [inner_smul_right] }
  have hinj : Function.Injective T := by
    intro y z hyz
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply HirschPolynomialAccess.vertex_tight_rows_span_checked d n a b x hx
    intro i hi
    by_cases hai : a i ∈ U
    · have hy : ⟪a i, (y : EuclideanSpace ℝ (Fin d))⟫ = 0 :=
        (U.mem_orthogonal _).mp y.2 (a i) hai
      have hz : ⟪a i, (z : EuclideanSpace ℝ (Fin d))⟫ = 0 :=
        (U.mem_orthogonal _).mp z.2 (a i) hai
      rw [inner_sub_right, hy, hz, sub_self]
    · have hiS : i ∈ S := by simp [S, hai, hi]
      have hcoord := congrFun hyz ⟨i, hiS⟩
      change ⟪a i, (y : EuclideanSpace ℝ (Fin d))⟫ =
        ⟪a i, (z : EuclideanSpace ℝ (Fin d))⟫ at hcoord
      rw [inner_sub_right, hcoord, sub_self]
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hcod : Module.finrank ℝ (S → ℝ) = S.card := by
    simp [Fintype.card_coe]
  have hdim : Module.finrank ℝ U + Module.finrank ℝ Uᗮ = d := by
    simpa only [finrank_euclideanSpace_fin] using U.finrank_add_finrank_orthogonal
  change d - Module.finrank ℝ U ≤ S.card
  rw [hcod] at hle
  omega

/-- A supporting row restricted to an extreme face of the parent. -/
def rowSection {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Set (EuclideanSpace ℝ (Fin d))) (i : Fin n) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  F ∩ HirschBalancedFaceCover.rowSupportingFace a b i

lemma rowSection_isExtreme {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Set (EuclideanSpace ℝ (Fin d))) (hF : IsExtreme ℝ (Hpoly a b) F)
    (i : Fin n) : IsExtreme ℝ F (rowSection a b F i) := by
  exact (hF.inter (HirschBalancedFaceCover.rowSupportingFace_isExtreme a b i)).mono
    hF.subset inter_subset_left

/-- All row normals whose equations hold throughout F, not merely the rows
originally chosen to describe F. This saturation prevents a rank-increasing
row from defining F again. -/
def faceRowSpan {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Set (EuclideanSpace ℝ (Fin d))) :
    Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  Submodule.span ℝ {z | ∃ i, z = a i ∧ ∀ x ∈ F, ⟪a i, x⟫ = b i}

lemma faceRowSpan_mono {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {F G : Set (EuclideanSpace ℝ (Fin d))} (hGF : G ⊆ F) :
    faceRowSpan a b F ≤ faceRowSpan a b G := by
  apply Submodule.span_mono
  rintro z ⟨i, hzi, hi⟩
  exact ⟨i, hzi, fun x hx => hi x (hGF hx)⟩

/-- A selected row gives a proper subset, including the possibility that
this child is empty. Empty children do not create false geometric progress. -/
lemma rowSection_ne_of_not_mem_faceRowSpan {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Set (EuclideanSpace ℝ (Fin d))) (i : Fin n)
    (hi : a i ∉ faceRowSpan a b F) : rowSection a b F i ≠ F := by
  intro heq
  apply hi
  apply Submodule.subset_span
  refine ⟨i, rfl, ?_⟩
  intro x hx
  have hxcut : x ∈ rowSection a b F i := by rw [heq]; exact hx
  exact hxcut.2.2

/-- The saturated normal span strictly grows at every selected cut. -/
theorem faceRowSpan_lt_rowSection {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Set (EuclideanSpace ℝ (Fin d))) (i : Fin n)
    (hi : a i ∉ faceRowSpan a b F) :
    faceRowSpan a b F < faceRowSpan a b (rowSection a b F i) := by
  have hsub : rowSection a b F i ⊆ F := inter_subset_left
  refine lt_of_le_of_ne (faceRowSpan_mono a b hsub) ?_
  intro heq
  apply hi
  rw [heq]
  apply Submodule.subset_span
  exact ⟨i, rfl, fun x hx => hx.2.2⟩

/-- In finite dimension the selected cuts strictly increase normal rank. -/
theorem faceRowSpan_finrank_lt_rowSection {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Set (EuclideanSpace ℝ (Fin d))) (i : Fin n)
    (hi : a i ∉ faceRowSpan a b F) :
    Module.finrank ℝ (faceRowSpan a b F) <
      Module.finrank ℝ (faceRowSpan a b (rowSection a b F i)) :=
  Submodule.finrank_lt_finrank_of_lt (faceRowSpan_lt_rowSection a b F i hi)

/-- Rank-sensitive averaging with no charge and no diameter hypothesis for
rows in U. Only selected sections need intrinsic bounds. For geometrically
proper children use the saturated space faceRowSpan a b F as U. -/
theorem diamLE_of_rank_increasing_row_bounds {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Set (EuclideanSpace ℝ (Fin d))) (hF : IsExtreme ℝ (Hpoly a b) F)
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hU : Module.finrank ℝ U < d)
    (B : Fin n → ℕ)
    (hFD : ∀ i, a i ∉ U → DiamLE (rowSection a b F i) (B i))
    (hconnect : ∀ u ∈ extremePoints ℝ F, ∀ v ∈ extremePoints ℝ F,
      ∃ L, HirschFaceSplice.Walk F L u v) :
    DiamLE F
      ((∑ i ∈ Finset.univ.filter (fun i => a i ∉ U), (B i + 1)) /
        (d - Module.finrank ℝ U) - 1) := by
  classical
  let weight : Fin n → ℕ := fun i => if a i ∈ U then 0 else 1
  have hcover : ∀ x ∈ extremePoints ℝ F,
      d - Module.finrank ℝ U ≤
        ∑ i, if x ∈ rowSection a b F i then weight i else 0 := by
    intro x hx
    have hxP : x ∈ extremePoints ℝ (Hpoly a b) :=
      hF.extremePoints_subset_extremePoints hx
    have hcount := tight_rows_outside_subspace_card_ge_codim a b x hxP U
    have heq :
        (∑ i, if x ∈ rowSection a b F i then weight i else 0) =
        (Finset.univ.filter (fun i => a i ∉ U ∧ ⟪a i, x⟫ = b i)).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hai : a i ∈ U <;> by_cases ht : ⟪a i, x⟫ = b i <;>
        simp [rowSection, HirschBalancedFaceCover.rowSupportingFace, weight,
          hx.1, hxP.1, hai, ht]
    rw [heq]
    exact hcount
  have hbound := HirschFaceSplice.diamLE_of_weighted_face_cover
    d (d - Module.finrank ℝ U) (by omega) F (rowSection a b F) B weight
    (rowSection_isExtreme a b F hF)
    (fun i hi => hFD i (by intro hai; simp [weight, hai] at hi))
    hcover hconnect
  have hcost : (∑ i, weight i * (B i + 1)) =
      ∑ i ∈ Finset.univ.filter (fun i => a i ∉ U), (B i + 1) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hai : a i ∈ U <;> simp [weight, hai]
  rw [hcost] at hbound
  exact hbound

#print axioms tight_rows_outside_subspace_card_ge_codim
#print axioms rowSection_isExtreme
#print axioms faceRowSpan_mono
#print axioms rowSection_ne_of_not_mem_faceRowSpan
#print axioms faceRowSpan_lt_rowSection
#print axioms faceRowSpan_finrank_lt_rowSection
#print axioms diamLE_of_rank_increasing_row_bounds

end HirschRankFaceCover
