import Mathlib
import Solutions.PolynomialCommonFaceTransport

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 3500000

noncomputable section

namespace HirschPolynomialAccess

/-- An H-presentation admits an equivalent subpresentation using at most `M`
of its original rows. This counts genuinely needed inequalities rather than
all nonzero restricted normals. -/
def HasSubpresentationAtMost {r n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin r)) (b : Fin n → ℝ) (M : ℕ) : Prop :=
  ∃ m : ℕ, m ≤ M ∧ ∃ e : Fin m ↪ Fin n,
    Hpoly (fun j => a (e j)) (fun j => b (e j)) = Hpoly a b

/-- Sparse-presentation condition for a common-face coordinate polytope. -/
def CommonFaceHasSubpresentationAtMost {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (p q : EuclideanSpace ℝ (Fin d)) (M : ℕ) : Prop :=
  HasSubpresentationAtMost
    (commonFaceA a b p q) (commonFaceB a b p q) M

def sparsePadA {r m : ℕ}
    (a : Fin m → EuclideanSpace ℝ (Fin r)) :
    Fin (2 * r) → EuclideanSpace ℝ (Fin r) :=
  fun i => if h : (i : ℕ) < m then a ⟨i, h⟩ else 0

def sparsePadB {r m : ℕ} (b : Fin m → ℝ) : Fin (2 * r) → ℝ :=
  fun i => if h : (i : ℕ) < m then b ⟨i, h⟩ else 1

lemma hpoly_sparsePad {r m : ℕ} (hm : m ≤ 2 * r)
    (a : Fin m → EuclideanSpace ℝ (Fin r)) (b : Fin m → ℝ) :
    Hpoly (sparsePadA a) (sparsePadB b) = Hpoly a b := by
  ext x
  simp only [Hpoly, mem_setOf_eq, sparsePadA, sparsePadB]
  constructor
  · intro hx i
    have hi : (i : ℕ) < 2 * r := lt_of_lt_of_le i.isLt hm
    simpa [i.isLt] using hx ⟨i, hi⟩
  · intro hx i
    by_cases hi : (i : ℕ) < m
    · simpa [hi] using hx ⟨i, hi⟩
    · simp [hi, inner_zero_left]

/-- Any r-dimensional H-polytope with an equivalent subpresentation of at
most `2r` rows may use an exactly balanced `2r`-row diameter theorem. -/
theorem diamLE_of_sparse_balanced_presentation
    {r n B : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin r)) (b : Fin n → ℝ)
    (hsparse : HasSubpresentationAtMost a b (2 * r))
    (hbalanced : ∀
      (a' : Fin (2 * r) → EuclideanSpace ℝ (Fin r))
      (b' : Fin (2 * r) → ℝ),
      (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
      DiamLE (Hpoly a' b') B)
    (hne : (Hpoly a b).Nonempty)
    (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) B := by
  obtain ⟨m, hm, e, hsub⟩ := hsparse
  let ae : Fin m → EuclideanSpace ℝ (Fin r) := fun j => a (e j)
  let be : Fin m → ℝ := fun j => b (e j)
  let ap := sparsePadA ae
  let bp := sparsePadB be
  have hpad : Hpoly ap bp = Hpoly a b := by
    calc
      Hpoly ap bp = Hpoly ae be := hpoly_sparsePad hm ae be
      _ = Hpoly a b := hsub
  have hne' : (Hpoly ap bp).Nonempty := by simpa only [hpad] using hne
  have hbd' : Bornology.IsBounded (Hpoly ap bp) := by simpa only [hpad] using hbd
  have hD := hbalanced ap bp hne' hbd'
  simpa only [hpad] using hD

/-- Common-face specialization of the sparse balanced-presentation bridge. -/
theorem commonFace_coord_diam_of_sparse_balanced
    {d n B : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (p q : EuclideanSpace ℝ (Fin d))
    (hsparse : CommonFaceHasSubpresentationAtMost a b p q
      (2 * commonFaceDim a b p q))
    (hbalanced : ∀
      (a' : Fin (2 * commonFaceDim a b p q) →
        EuclideanSpace ℝ (Fin (commonFaceDim a b p q)))
      (b' : Fin (2 * commonFaceDim a b p q) → ℝ),
      (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
      DiamLE (Hpoly a' b') B)
    (hne : (Hpoly (commonFaceA a b p q) (commonFaceB a b p q)).Nonempty)
    (hbd : Bornology.IsBounded
      (Hpoly (commonFaceA a b p q) (commonFaceB a b p q))) :
    DiamLE (Hpoly (commonFaceA a b p q) (commonFaceB a b p q)) B := by
  exact diamLE_of_sparse_balanced_presentation
    (commonFaceA a b p q) (commonFaceB a b p q) hsparse hbalanced hne hbd

#print axioms diamLE_of_sparse_balanced_presentation
#print axioms commonFace_coord_diam_of_sparse_balanced

end HirschPolynomialAccess
