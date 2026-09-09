import Mathlib
import Solutions.PolynomialCommonFaceTransport

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschPolynomialAccess

/-- Rows whose normals remain nonzero after restriction to the common-face
direction space. All other rows are tautological in common-face coordinates
whenever the source point is feasible. -/
noncomputable def commonFaceEffectiveRows {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => commonFaceA a b u x i ≠ 0)

noncomputable def commonFaceEffectiveCount {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) : ℕ :=
  (commonFaceEffectiveRows a b u x).card

lemma commonFaceB_nonneg_of_mem {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b) (i : Fin n) :
    0 ≤ commonFaceB a b u x i := by
  dsimp [commonFaceB]
  exact sub_nonneg.mpr (hu i)

theorem exists_commonFace_effective_model {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b) :
    ∃ e : Fin (commonFaceEffectiveCount a b u x) ↪ Fin n,
      Hpoly
        (fun j => commonFaceA a b u x (e j))
        (fun j => commonFaceB a b u x (e j)) =
      Hpoly (commonFaceA a b u x) (commonFaceB a b u x) := by
  classical
  let S := commonFaceEffectiveRows a b u x
  let E : Fin (commonFaceEffectiveCount a b u x) ≃ S := by
    simpa [commonFaceEffectiveCount, S] using (Fintype.equivFin S).symm
  let e : Fin (commonFaceEffectiveCount a b u x) ↪ Fin n :=
    { toFun := fun j => (E j).val
      inj' := by
        intro j k h
        exact E.injective (Subtype.ext h) }
  have hesurj : ∀ i ∈ S,
      ∃ j : Fin (commonFaceEffectiveCount a b u x), e j = i := by
    intro i hi
    refine ⟨E.symm ⟨i, hi⟩, ?_⟩
    change (E (E.symm ⟨i, hi⟩)).val = i
    rw [E.apply_symm_apply]
  refine ⟨e, ?_⟩
  ext q
  constructor
  · intro hq i
    by_cases hi : i ∈ S
    · obtain ⟨j, hj⟩ := hesurj i hi
      have hjq := hq j
      change ⟪commonFaceA a b u x (e j), q⟫ ≤
        commonFaceB a b u x (e j) at hjq
      simpa only [hj] using hjq
    · have hzero : commonFaceA a b u x i = 0 := by
        simpa [S, commonFaceEffectiveRows] using hi
      rw [hzero, inner_zero_left]
      exact commonFaceB_nonneg_of_mem a b u x hu i
  · intro hq j
    exact hq (e j)

def padToBalancedA {r m : ℕ}
    (a : Fin m → EuclideanSpace ℝ (Fin r)) :
    Fin (2 * r) → EuclideanSpace ℝ (Fin r) :=
  fun i => if h : (i : ℕ) < m then a ⟨i, h⟩ else 0

def padToBalancedB {r m : ℕ} (b : Fin m → ℝ) : Fin (2 * r) → ℝ :=
  fun i => if h : (i : ℕ) < m then b ⟨i, h⟩ else 1

lemma hpoly_padToBalanced {r m : ℕ} (hm : m ≤ 2 * r)
    (a : Fin m → EuclideanSpace ℝ (Fin r)) (b : Fin m → ℝ) :
    Hpoly (padToBalancedA a) (padToBalancedB b) = Hpoly a b := by
  ext q
  simp only [Hpoly, mem_setOf_eq, padToBalancedA, padToBalancedB]
  constructor
  · intro h i
    have hi : (i : ℕ) < 2 * r := lt_of_lt_of_le i.isLt hm
    simpa [i.isLt] using h ⟨i, hi⟩
  · intro h i
    by_cases hi : (i : ℕ) < m
    · simpa [hi] using h ⟨i, hi⟩
    · simp [hi, inner_zero_left]

theorem exists_balanced_commonFace_model {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b)
    (heff : commonFaceEffectiveCount a b u x ≤ 2 * commonFaceDim a b u x) :
    ∃ a' : Fin (2 * commonFaceDim a b u x) →
          EuclideanSpace ℝ (Fin (commonFaceDim a b u x)),
      ∃ b' : Fin (2 * commonFaceDim a b u x) → ℝ,
        Hpoly a' b' =
          Hpoly (commonFaceA a b u x) (commonFaceB a b u x) := by
  obtain ⟨e, he⟩ := exists_commonFace_effective_model a b u x hu
  let ae := fun j => commonFaceA a b u x (e j)
  let be := fun j => commonFaceB a b u x (e j)
  refine ⟨padToBalancedA ae, padToBalancedB be, ?_⟩
  rw [hpoly_padToBalanced heff ae be]
  exact he

theorem commonFace_coord_diam_of_balanced_effective
    {d n B : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b)
    (heff : commonFaceEffectiveCount a b u x ≤ 2 * commonFaceDim a b u x)
    (hbalanced : ∀
      (a' : Fin (2 * commonFaceDim a b u x) →
        EuclideanSpace ℝ (Fin (commonFaceDim a b u x)))
      (b' : Fin (2 * commonFaceDim a b u x) → ℝ),
      (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
      DiamLE (Hpoly a' b') B)
    (hne : (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)).Nonempty)
    (hbd : Bornology.IsBounded
      (Hpoly (commonFaceA a b u x) (commonFaceB a b u x))) :
    DiamLE (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)) B := by
  obtain ⟨a', b', hP⟩ := exists_balanced_commonFace_model a b u x hu heff
  have hne' : (Hpoly a' b').Nonempty := by simpa only [hP] using hne
  have hbd' : Bornology.IsBounded (Hpoly a' b') := by simpa only [hP] using hbd
  have hD := hbalanced a' b' hne' hbd'
  simpa only [hP] using hD

#print axioms exists_commonFace_effective_model
#print axioms exists_balanced_commonFace_model
#print axioms commonFace_coord_diam_of_balanced_effective

end HirschPolynomialAccess
