import Mathlib
import Solutions.PolynomialCommonFaceTransport
import Solutions.PolynomialProductWalk

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 4500000

noncomputable section

namespace HirschPolynomialAccess

lemma explicit_bridge_adj_reverse {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {u v : E} (h : Adj P u v) : Adj P v u := by
  refine ⟨Ne.symm h.1, ?_⟩
  simpa only [segment_symm] using h.2

lemma explicit_bridge_extreme_of_face
    {d : ℕ}
    {P F : Set (EuclideanSpace ℝ (Fin d))}
    (hF : IsExtreme ℝ P F)
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ extremePoints ℝ P) (hxF : x ∈ F) :
    x ∈ extremePoints ℝ F := by
  refine ⟨hxF, ?_⟩
  intro p hp q hq hopen
  exact hx.2 (hF.1 hp) (hF.1 hq) hopen

/-- Lift an edge walk in an extreme face to an edge walk in the parent. -/
lemma explicit_bridge_face_walk_to_parent
    {d B : ℕ}
    {P F : Set (EuclideanSpace ℝ (Fin d))}
    (hF : IsExtreme ℝ P F)
    {u v : EuclideanSpace ℝ (Fin d)}
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (h0 : w 0 = u) (hB : w B = v)
    (hs : ∀ j < B, w j = w (j + 1) ∨ Adj F (w j) (w (j + 1))) :
    ∀ j < B, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)) := by
  intro j hj
  rcases hs j hj with heq | hadj
  · exact Or.inl heq
  · exact Or.inr ⟨hadj.1, hF.trans hadj.2⟩

/-- Reverse a padded parent-edge walk. -/
lemma explicit_bridge_reverse_walk
    {d B : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    {u v : EuclideanSpace ℝ (Fin d)}
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (h0 : w 0 = u) (hB : w B = v)
    (hs : ∀ j < B, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∃ wr : ℕ → EuclideanSpace ℝ (Fin d), wr 0 = v ∧ wr B = u ∧
      ∀ j < B, wr j = wr (j + 1) ∨ Adj P (wr j) (wr (j + 1)) := by
  let wr : ℕ → EuclideanSpace ℝ (Fin d) := fun j => w (B - j)
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
        have hrev := explicit_bridge_adj_reverse hadj
        simpa only [heq] using hrev)

/-- The exact routing mechanism behind the proposed 2-face bridge argument.

Let `F` be any extreme face containing `u` and a bridge vertex `z`. If `F`
has diameter at most `A`, and `v,z` lie in a common face of dimension at most
2 whose coordinate H-polytope has diameter at most `2d`, then `u` reaches `v`
in `A+2d` parent edges.  The low-dimensional bound is supplied explicitly;
no conjectural bridge-existence assumption is hidden here. -/
theorem walk_of_explicit_face_two_face_bridge
    (d A : ℕ)
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d))
    (b : Fin (2 * d) → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (F : Set (EuclideanSpace ℝ (Fin d)))
    (hF : IsExtreme ℝ (Hpoly a b) F)
    (u v z : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hz : z ∈ extremePoints ℝ (Hpoly a b))
    (huF : u ∈ F) (hzF : z ∈ F)
    (hFD : DiamLE F A)
    (htargetDim : commonFaceDim a b v z ≤ 2)
    (hlow2 : ∀ e : ℕ, e ≤ 2 →
      ∀ (a' : Fin (2 * d) → EuclideanSpace ℝ (Fin e))
        (b' : Fin (2 * d) → ℝ),
        (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
        DiamLE (Hpoly a' b') (2 * d)) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
      w 0 = u ∧ w (A + 2 * d) = v ∧
      ∀ j < A + 2 * d,
        w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  let P := Hpoly a b
  have huFext : u ∈ extremePoints ℝ F :=
    explicit_bridge_extreme_of_face hF hu huF
  have hzFext : z ∈ extremePoints ℝ F :=
    explicit_bridge_extreme_of_face hF hz hzF
  obtain ⟨ws, hws0, hwsA, hwsF⟩ := hFD u huFext z hzFext
  have hwsP : ∀ j < A,
      ws j = ws (j + 1) ∨ Adj P (ws j) (ws (j + 1)) :=
    explicit_bridge_face_walk_to_parent hF ws hws0 hwsA hwsF

  let et := commonFaceDim a b v z
  let Qt := Hpoly (commonFaceA a b v z) (commonFaceB a b v z)
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
    explicit_bridge_reverse_walk P wt hwt0 hwtB hwtstep

  exact HirschProduct.append_walk (Adj P) ws wr
    hws0 hwsA hwr0 hwrB hwsP hwrstep

/-- Quadratic specialization. If the containing bridge face has the previous
quadratic budget `(d-1)^2+(d-1)`, the linear two-face repair closes at exactly
`d^2+d`. -/
theorem quadratic_walk_of_explicit_two_face_bridge
    (d : ℕ) (hd : 0 < d)
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d))
    (b : Fin (2 * d) → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (F : Set (EuclideanSpace ℝ (Fin d)))
    (hF : IsExtreme ℝ (Hpoly a b) F)
    (u v z : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hz : z ∈ extremePoints ℝ (Hpoly a b))
    (huF : u ∈ F) (hzF : z ∈ F)
    (hFD : DiamLE F ((d - 1) ^ 2 + (d - 1)))
    (htargetDim : commonFaceDim a b v z ≤ 2)
    (hlow2 : ∀ e : ℕ, e ≤ 2 →
      ∀ (a' : Fin (2 * d) → EuclideanSpace ℝ (Fin e))
        (b' : Fin (2 * d) → ℝ),
        (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
        DiamLE (Hpoly a' b') (2 * d)) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
      w 0 = u ∧ w (d ^ 2 + d) = v ∧
      ∀ j < d ^ 2 + d,
        w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  obtain ⟨w0, hw00, hw0B, hw0step⟩ :=
    walk_of_explicit_face_two_face_bridge d ((d - 1) ^ 2 + (d - 1))
      a b hbd F hF u v z hu hv hz huF hzF hFD htargetDim hlow2
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  have hlen : (k + 1 - 1) ^ 2 + (k + 1 - 1) + 2 * (k + 1) =
      (k + 1) ^ 2 + (k + 1) := by
    simp
    ring
  simpa only [hlen] using ⟨w0, hw00, hw0B, hw0step⟩

/-- Polytope-level conditional quadratic theorem. Every ordered vertex pair
is assumed to admit an explicit extreme bridge face with the previous
quadratic diameter budget and a bridge vertex 2-adjacent to the target. -/
theorem quadratic_diameter_of_explicit_two_face_bridge_property
    (d : ℕ) (hd : 0 < d)
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d))
    (b : Fin (2 * d) → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hbridge : ∀ u ∈ extremePoints ℝ (Hpoly a b),
      ∀ v ∈ extremePoints ℝ (Hpoly a b),
      ∃ (F : Set (EuclideanSpace ℝ (Fin d)))
        (z : EuclideanSpace ℝ (Fin d)),
        IsExtreme ℝ (Hpoly a b) F ∧
        z ∈ extremePoints ℝ (Hpoly a b) ∧
        u ∈ F ∧ z ∈ F ∧
        DiamLE F ((d - 1) ^ 2 + (d - 1)) ∧
        commonFaceDim a b v z ≤ 2)
    (hlow2 : ∀ e : ℕ, e ≤ 2 →
      ∀ (a' : Fin (2 * d) → EuclideanSpace ℝ (Fin e))
        (b' : Fin (2 * d) → ℝ),
        (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
        DiamLE (Hpoly a' b') (2 * d)) :
    DiamLE (Hpoly a b) (d ^ 2 + d) := by
  intro u hu v hv
  obtain ⟨F, z, hF, hz, huF, hzF, hFD, h2⟩ := hbridge u hu v hv
  exact quadratic_walk_of_explicit_two_face_bridge
    d hd a b hbd F hF u v z hu hv hz huF hzF hFD h2 hlow2

#print axioms walk_of_explicit_face_two_face_bridge
#print axioms quadratic_walk_of_explicit_two_face_bridge
#print axioms quadratic_diameter_of_explicit_two_face_bridge_property

end HirschPolynomialAccess
