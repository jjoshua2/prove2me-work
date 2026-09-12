import Mathlib
import Definitions.Def_Hirsch_model
import Solutions.PolynomialClipEndpointLift

open scoped RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschSaturatedRank

/-- The supporting equality face cut out by one describing row. -/
def rowSupportingFace {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (i : Fin n) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  Hpoly a b ∩ {x | ⟪a i, x⟫ = b i}

lemma rowSupportingFace_isExtreme {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (i : Fin n) :
    IsExtreme ℝ (Hpoly a b) (rowSupportingFace a b i) := by
  exact HirschClipLift.supporting_equality_extreme
    (Hpoly a b) (a i) (b i) (fun z hz => hz i)

/-- Restrict a parent extreme face to one additional describing equality. -/
def rowSection {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Set (EuclideanSpace ℝ (Fin d))) (i : Fin n) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  F ∩ rowSupportingFace a b i

lemma rowSection_isExtreme {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Set (EuclideanSpace ℝ (Fin d))) (hF : IsExtreme ℝ (Hpoly a b) F)
    (i : Fin n) : IsExtreme ℝ F (rowSection a b F i) := by
  exact (hF.inter (rowSupportingFace_isExtreme a b i)).mono
    hF.subset inter_subset_left

/-- Saturated normal span of a parent face: include every describing row whose
equality holds throughout the whole face, not only rows originally chosen to
describe it. This avoids fake rank progress from redundant row labels. -/
def faceRowSpan {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Set (EuclideanSpace ℝ (Fin d))) :
    Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  Submodule.span ℝ {z | ∃ i, z = a i ∧ ∀ x ∈ F, ⟪a i, x⟫ = b i}

/-- Shrinking a face can only enlarge its saturated tight-normal span. -/
lemma faceRowSpan_mono {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {F G : Set (EuclideanSpace ℝ (Fin d))} (hGF : G ⊆ F) :
    faceRowSpan a b F ≤ faceRowSpan a b G := by
  apply Submodule.span_mono
  rintro z ⟨i, hzi, hi⟩
  exact ⟨i, hzi, fun x hx => hi x (hGF hx)⟩

/-- If the selected normal is absent from the SATURATED span, imposing its
equality cannot leave the face unchanged. -/
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

/-- A genuinely new supporting cut strictly grows the saturated normal span. -/
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

/-- In finite dimension every genuinely new saturated supporting cut increases
normal rank by at least one. -/
theorem faceRowSpan_finrank_lt_rowSection {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Set (EuclideanSpace ℝ (Fin d))) (i : Fin n)
    (hi : a i ∉ faceRowSpan a b F) :
    Module.finrank ℝ (faceRowSpan a b F) <
      Module.finrank ℝ (faceRowSpan a b (rowSection a b F i)) :=
  Submodule.finrank_lt_finrank_of_lt (faceRowSpan_lt_rowSection a b F i hi)

/-- Every saturated face-normal span has rank at most the ambient dimension. -/
theorem faceRowSpan_finrank_le_dim {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Set (EuclideanSpace ℝ (Fin d))) :
    Module.finrank ℝ (faceRowSpan a b F) ≤ d := by
  simpa only [finrank_euclideanSpace_fin] using
    Submodule.finrank_le (faceRowSpan a b F)

#print axioms rowSupportingFace_isExtreme
#print axioms rowSection_isExtreme
#print axioms faceRowSpan_mono
#print axioms rowSection_ne_of_not_mem_faceRowSpan
#print axioms faceRowSpan_lt_rowSection
#print axioms faceRowSpan_finrank_lt_rowSection
#print axioms faceRowSpan_finrank_le_dim

end HirschSaturatedRank
