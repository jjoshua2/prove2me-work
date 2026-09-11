import Mathlib
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 3000000
set_option autoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschExcessTwo

/-- Normalized slack model for an H-polytope with row excess two:
nonnegative coordinates with total mass one and one affine moment. -/
def momentSlice {n : ℕ} (t : Fin n → ℝ) (mu : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {s | (∀ i, 0 ≤ s i) ∧ (∑ i, s i) = 1 ∧ (∑ i, t i * s i) = mu}

/-- The coordinate-zero support face of a normalized moment slice. -/
def zeroFace {n : ℕ} (t : Fin n → ℝ) (mu : ℝ) (i : Fin n) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {s | s ∈ momentSlice t mu ∧ s i = 0}

lemma zeroFace_subset {n : ℕ} (t : Fin n → ℝ) (mu : ℝ) (i : Fin n) :
    zeroFace t mu i ⊆ momentSlice t mu := by
  intro s hs
  exact hs.1

/-- Nonnegativity makes every coordinate-zero support condition an extreme
face. This is the basic face-preservation fact used by the excess-two portal
selector. -/
theorem zeroFace_isExtreme {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i : Fin n) :
    IsExtreme ℝ (momentSlice t mu) (zeroFace t mu i) := by
  refine ⟨zeroFace_subset t mu i, ?_⟩
  intro x hx y hy z hz hzseg
  rcases (mem_openSegment_iff_div.mp hzseg) with ⟨a, b, ha, hb, hcomb⟩
  have hab : 0 < a + b := add_pos ha hb
  have hapos : 0 < a / (a + b) := div_pos ha hab
  have hbpos : 0 < b / (a + b) := div_pos hb hab
  have hxnon : 0 ≤ x i := hx.1 i
  have hynon : 0 ≤ y i := hy.1 i
  have hz0 : z i = 0 := hz.2
  have hcoord : (a / (a + b)) * x i + (b / (a + b)) * y i = z i := by
    have h := congrArg (fun q : EuclideanSpace ℝ (Fin n) => q i) hcomb
    simpa [smul_eq_mul] using h
  have hxi : x i = 0 := by
    rw [hz0] at hcoord
    nlinarith
  exact ⟨hx, hxi⟩

#print axioms zeroFace_isExtreme

end HirschExcessTwo
