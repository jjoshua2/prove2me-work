import Mathlib
import Solutions.PolynomialFaceSparsePresentation
import Solutions.PolynomialProductWalk

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 5000000

noncomputable section

namespace HirschPolynomialAccess

lemma bridge_adj_reverse {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {u v : E} (h : Adj P u v) : Adj P v u := by
  refine ⟨Ne.symm h.1, ?_⟩
  simpa only [segment_symm] using h.2

/-- Reverse a padded edge walk while keeping the same exact budget. -/
lemma reverse_padded_walk {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Set E) {B : ℕ} {u v : E}
    (w : ℕ → E) (h0 : w 0 = u) (hB : w B = v)
    (hs : ∀ j < B, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∃ wr : ℕ → E, wr 0 = v ∧ wr B = u ∧
      ∀ j < B, wr j = wr (j + 1) ∨ Adj P (wr j) (wr (j + 1)) := by
  let wr : ℕ → E := fun j => w (B - j)
  refine ⟨wr, ?_, ?_, ?_⟩
  · simpa [wr] using hB
  · simpa [wr] using h0
  · intro j hj
    have hk : B - (j + 1) < B := by omega
    have heq : B - (j + 1) + 1 = B - j := by omega
    rcases hs (B - (j + 1)) hk with hsame | hadj
    · exact Or.inl (by
        change w (B - j) = w (B - (j + 1))
        simpa only [heq] using hsame.symm)
    · exact Or.inr (by
        change Adj P (w (B - j)) (w (B - (j + 1)))
        have hrev := bridge_adj_reverse hadj
        simpa only [heq] using hrev)

/-- Pair-level quadratic consequence of a 2-face bridge.

Suppose `z` lies with `u` in a lower-dimensional common face whose coordinate
polytope has an equivalent presentation by at most twice its dimension rows.
Assume balanced polytopes in every smaller dimension `e<d` have diameter at
most `e^2+e`. If in addition `v` and `z` lie in a common face of dimension at
most two, and all such at-most-two-dimensional `2d`-row coordinate polytopes
have diameter at most `2d`, then `u` reaches `v` within `d^2+d` parent edges.

This is the formal recurrence behind the historical proposed 2-face bridge
approach: the source-side cost is inductive and the 2-face repair is linear. -/
theorem quadratic_walk_of_sparse_two_face_bridge
    (d : ℕ)
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d))
    (b : Fin (2 * d) → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v z : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hz : z ∈ extremePoints ℝ (Hpoly a b))
    (hsourceDim : commonFaceDim a b u z < d)
    (hsourceSparse : CommonFaceHasSubpresentationAtMost a b u z
      (2 * commonFaceDim a b u z))
    (htargetDim : commonFaceDim a b v z ≤ 2)
    (hsmall : ∀ e : ℕ, e < d →
      ∀ (a' : Fin (2 * e) → EuclideanSpace ℝ (Fin e))
        (b' : Fin (2 * e) → ℝ),
        (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
        DiamLE (Hpoly a' b') (e ^ 2 + e))
    (hlow2 : ∀ e : ℕ, e ≤ 2 →
      ∀ (a' : Fin (2 * d) → EuclideanSpace ℝ (Fin e))
        (b' : Fin (2 * d) → ℝ),
        (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
        DiamLE (Hpoly a' b') (2 * d)) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
      w 0 = u ∧ w (d ^ 2 + d) = v ∧
      ∀ j < d ^ 2 + d,
        w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  let P := Hpoly a b
  let es := commonFaceDim a b u z
  let et := commonFaceDim a b v z
  let Qs := Hpoly (commonFaceA a b u z) (commonFaceB a b u z)
  let Qt := Hpoly (commonFaceA a b v z) (commonFaceB a b v z)

  have hQsne : Qs.Nonempty := by
    obtain ⟨q, hq, _⟩ := commonFacePoint_surjOn a b u z
      (commonFace_u_mem a b u z hu.1)
    exact ⟨q, hq⟩
  have hQsbd : Bornology.IsBounded Qs :=
    commonFace_coord_bounded a b u z hbd
  have hsourceBalanced : ∀
      (a' : Fin (2 * es) → EuclideanSpace ℝ (Fin es))
      (b' : Fin (2 * es) → ℝ),
      (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
      DiamLE (Hpoly a' b') (es ^ 2 + es) := by
    exact hsmall es (by simpa [es] using hsourceDim)
  have hDs : DiamLE Qs (es ^ 2 + es) := by
    dsimp [Qs, es]
    exact commonFace_coord_diam_of_sparse_balanced
      a b u z hsourceSparse hsourceBalanced hQsne hQsbd
  obtain ⟨ws, hws0, hwsB, hwsstep⟩ :=
    common_face_walk_of_coord_diam a b u z hu hz (es ^ 2 + es) hDs

  have hQtne : Qt.Nonempty := by
    obtain ⟨q, hq, _⟩ := commonFacePoint_surjOn a b v z
      (commonFace_u_mem a b v z hv.1)
    exact ⟨q, hq⟩
  have hQtbd : Bornology.IsBounded Qt :=
    commonFace_coord_bounded a b v z hbd
  have hDt : DiamLE Qt (2 * d) := by
    dsimp [Qt, et]
    exact hlow2 (commonFaceDim a b v z) htargetDim
      (commonFaceA a b v z) (commonFaceB a b v z) hQtne hQtbd
  obtain ⟨wt, hwt0, hwtB, hwtstep⟩ :=
    common_face_walk_of_coord_diam a b v z hv hz (2 * d) hDt
  obtain ⟨wr, hwr0, hwrB, hwrstep⟩ :=
    reverse_padded_walk P wt hwt0 hwtB hwtstep

  obtain ⟨w0, hw00, hw0B, hw0step⟩ :=
    HirschProduct.append_walk (Adj P) ws wr
      hws0 hwsB hwr0 hwrB hwsstep hwrstep

  have hdpos : 0 < d := by
    exact lt_of_le_of_lt (Nat.zero_le es) hsourceDim
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdpos)
  subst d
  have hesle : es ≤ k := by
    simpa using hsourceDim
  have hprod : es * (es + 1) ≤ k * (k + 1) :=
    Nat.mul_le_mul hesle (Nat.add_le_add_right hesle 1)
  have hbudget : es ^ 2 + es + 2 * (k + 1) ≤ (k + 1) ^ 2 + (k + 1) := by
    calc
      es ^ 2 + es + 2 * (k + 1) = es * (es + 1) + 2 * (k + 1) := by ring
      _ ≤ k * (k + 1) + 2 * (k + 1) := Nat.add_le_add_right hprod _
      _ = (k + 1) ^ 2 + (k + 1) := by ring
  obtain ⟨w, hw0, hwB, hwstep⟩ :=
    HirschProduct.pad_walk (Adj P) hbudget w0 hw00 hw0B hw0step
  exact ⟨w, hw0, hwB, hwstep⟩

/-- Polytope-level version: if every ordered vertex pair admits such a sparse
source/2-face target bridge, the balanced polytope has quadratic diameter.
The low-dimensional planar bound is kept explicit so this theorem isolates
only the bridge mechanism. -/
theorem quadratic_diameter_of_two_face_bridge_property
    (d : ℕ)
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d))
    (b : Fin (2 * d) → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hbridge : ∀ u ∈ extremePoints ℝ (Hpoly a b),
      ∀ v ∈ extremePoints ℝ (Hpoly a b),
      ∃ z ∈ extremePoints ℝ (Hpoly a b),
        commonFaceDim a b u z < d ∧
        CommonFaceHasSubpresentationAtMost a b u z
          (2 * commonFaceDim a b u z) ∧
        commonFaceDim a b v z ≤ 2)
    (hsmall : ∀ e : ℕ, e < d →
      ∀ (a' : Fin (2 * e) → EuclideanSpace ℝ (Fin e))
        (b' : Fin (2 * e) → ℝ),
        (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
        DiamLE (Hpoly a' b') (e ^ 2 + e))
    (hlow2 : ∀ e : ℕ, e ≤ 2 →
      ∀ (a' : Fin (2 * d) → EuclideanSpace ℝ (Fin e))
        (b' : Fin (2 * d) → ℝ),
        (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
        DiamLE (Hpoly a' b') (2 * d)) :
    DiamLE (Hpoly a b) (d ^ 2 + d) := by
  intro u hu v hv
  obtain ⟨z, hz, hsd, hss, htd⟩ := hbridge u hu v hv
  exact quadratic_walk_of_sparse_two_face_bridge
    d a b hbd u v z hu hv hz hsd hss htd hsmall hlow2

#print axioms quadratic_walk_of_sparse_two_face_bridge
#print axioms quadratic_diameter_of_two_face_bridge_property

end HirschPolynomialAccess
