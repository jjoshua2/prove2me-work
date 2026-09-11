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

/-- A finite sum supported only on two distinct indices reduces to those two
terms. This is used repeatedly by the explicit moment-slice coordinates. -/
lemma sum_eq_add_of_zero_off_pair {n : ℕ}
    (f : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j)
    (hzero : ∀ k, k ≠ i → k ≠ j → f k = 0) :
    (∑ k, f k) = f i + f j := by
  classical
  have hsub : ({i, j} : Finset (Fin n)) ⊆ Finset.univ := by simp
  have hsmall :
      (∑ k ∈ ({i, j} : Finset (Fin n)), f k) =
        ∑ k ∈ (Finset.univ : Finset (Fin n)), f k := by
    apply Finset.sum_subset hsub
    intro k _ hk
    apply hzero k
    · intro hki
      subst k
      exact hk (by simp)
    · intro hkj
      subst k
      exact hk (by simp)
  calc
    (∑ k, f k) = ∑ k ∈ (Finset.univ : Finset (Fin n)), f k := rfl
    _ = ∑ k ∈ ({i, j} : Finset (Fin n)), f k := hsmall.symm
    _ = f i + f j := by simp [hij]

/-- The unique feasible point supported on a low index `i` and a high index
`j`. The hypotheses ensuring `t i < mu < t j` are supplied to the lemmas. -/
def pairPoint {n : ℕ} (t : Fin n → ℝ) (mu : ℝ) (i j : Fin n) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun k =>
    if k = i then (t j - mu) / (t j - t i)
    else if k = j then (mu - t i) / (t j - t i)
    else 0)

@[simp] lemma pairPoint_apply_left {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j : Fin n) :
    pairPoint t mu i j i = (t j - mu) / (t j - t i) := by
  simp [pairPoint]

@[simp] lemma pairPoint_apply_right {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j : Fin n) (hij : i ≠ j) :
    pairPoint t mu i j j = (mu - t i) / (t j - t i) := by
  simp [pairPoint, hij.symm]

@[simp] lemma pairPoint_apply_other {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j k : Fin n)
    (hki : k ≠ i) (hkj : k ≠ j) :
    pairPoint t mu i j k = 0 := by
  simp [pairPoint, hki, hkj]

/-- The explicit two-supported point satisfies the two moment equations. -/
theorem pairPoint_mem {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j : Fin n)
    (hli : t i < mu) (hrj : mu < t j) :
    pairPoint t mu i j ∈ momentSlice t mu := by
  classical
  have hij : i ≠ j := by
    intro h
    subst j
    linarith
  have hden : 0 < t j - t i := by linarith
  refine ⟨?_, ?_, ?_⟩
  · intro k
    by_cases hki : k = i
    · subst k
      rw [pairPoint_apply_left]
      positivity
    · by_cases hkj : k = j
      · subst k
        rw [pairPoint_apply_right t mu i j hij]
        positivity
      · rw [pairPoint_apply_other t mu i j k hki hkj]
  · have hsum := sum_eq_add_of_zero_off_pair
      (fun k => pairPoint t mu i j k) i j hij
      (fun k hki hkj => pairPoint_apply_other t mu i j k hki hkj)
    rw [hsum, pairPoint_apply_left, pairPoint_apply_right t mu i j hij]
    field_simp [ne_of_gt hden]
    ring
  · have hsum := sum_eq_add_of_zero_off_pair
      (fun k => t k * pairPoint t mu i j k) i j hij (by
        intro k hki hkj
        rw [pairPoint_apply_other t mu i j k hki hkj, mul_zero])
    rw [hsum, pairPoint_apply_left, pairPoint_apply_right t mu i j hij]
    field_simp [ne_of_gt hden]
    ring

#print axioms zeroFace_isExtreme
#print axioms sum_eq_add_of_zero_off_pair
#print axioms pairPoint_mem

end HirschExcessTwo
