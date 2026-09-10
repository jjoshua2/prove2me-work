import Mathlib
import Theorems.Thm_Hirsch_larman_bound
import Solutions.PolynomialCommonFaceTransport

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschPolynomialAccess

variable {d n : ℕ}

/-- Larman's theorem applied after coordinatizing the common-source face of two
vertices.  The resulting coordinate-edge walk maps back to a genuine edge
walk in the parent polytope. -/
theorem common_face_larman_walk
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hx : x ∈ extremePoints ℝ (Hpoly a b)) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
      w 0 = u ∧
      w (n * 2 ^ (commonFaceDim a b u x - 3)) = x ∧
      ∀ j < n * 2 ^ (commonFaceDim a b u x - 3),
        w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  let Q := Hpoly (commonFaceA a b u x) (commonFaceB a b u x)
  have huF : u ∈ commonFace a b u x :=
    commonFace_u_mem a b u x hu.1
  have hxF : x ∈ commonFace a b u x :=
    commonFace_x_mem a b u x hx.1
  have huFext : u ∈ extremePoints ℝ (commonFace a b u x) := by
    rw [(commonFace_isExtreme a b u x).extremePoints_eq]
    exact ⟨huF, hu⟩
  have hxFext : x ∈ extremePoints ℝ (commonFace a b u x) := by
    rw [(commonFace_isExtreme a b u x).extremePoints_eq]
    exact ⟨hxF, hx⟩
  obtain ⟨qu, hquQ, hqu⟩ := commonFacePoint_surjOn a b u x huF
  obtain ⟨qx, hqxQ, hqx⟩ := commonFacePoint_surjOn a b u x hxF
  have hquFext : commonFacePoint a b u x qu ∈
      extremePoints ℝ (commonFace a b u x) := by
    rw [hqu]
    exact huFext
  have hqxFext : commonFacePoint a b u x qx ∈
      extremePoints ℝ (commonFace a b u x) := by
    rw [hqx]
    exact hxFext
  have hquExt : qu ∈ extremePoints ℝ Q := by
    exact commonFace_coord_extreme_of_face_extreme a b u x hquFext
  have hqxExt : qx ∈ extremePoints ℝ Q := by
    exact commonFace_coord_extreme_of_face_extreme a b u x hqxFext
  have hQbd : Bornology.IsBounded Q :=
    commonFace_coord_bounded a b u x hbd
  have hQne : Q.Nonempty := ⟨qu, hquQ⟩
  obtain ⟨wq, hwq0, hwqB, hwqstep⟩ :=
    Hirsch.larman_bound (commonFaceDim a b u x) n
      (commonFaceA a b u x) (commonFaceB a b u x) hQne hQbd
      qu hquExt qx hqxExt
  let w : ℕ → EuclideanSpace ℝ (Fin d) :=
    fun j => commonFacePoint a b u x (wq j)
  refine ⟨w, ?_, ?_, ?_⟩
  · dsimp [w]
    rw [hwq0, hqu]
  · dsimp [w]
    rw [hwqB, hqx]
  · intro j hj
    rcases hwqstep j hj with heq | hadj
    · exact Or.inl (by simpa [w] using congrArg (commonFacePoint a b u x) heq)
    · exact Or.inr (by
        simpa [w] using commonFace_coord_adj_to_parent a b u x hadj)

/-- In a separated source/target instance, every target-avoiding vertex can be
reached from the source with a Larman bound whose dimension is at most the
facet excess `n - 2*d`.  This is the quantitative bridge from the rank lemma
to an excess-parameter walk bound. -/
theorem target_avoider_common_face_walk
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i)
    (havoid : ∀ i, a i ≠ 0 →
      ⟪a i, v⟫ = b i → ⟪a i, x⟫ ≠ b i) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
      w 0 = u ∧
      w (n * 2 ^ ((n - 2 * d) - 3)) = x ∧
      ∀ j < n * 2 ^ ((n - 2 * d) - 3),
        w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  have hD : commonFaceDim a b u x ≤ n - 2 * d := by
    simpa [commonFaceDim] using
      common_direction_finrank_le_excess a b u v x hu hv hx hsep havoid
  obtain ⟨w, hw0, hwD, hwstep⟩ := common_face_larman_walk a b u x hbd hu hx
  have hexp : commonFaceDim a b u x - 3 ≤ (n - 2 * d) - 3 :=
    Nat.sub_le_sub_right hD 3
  have hpow : 2 ^ (commonFaceDim a b u x - 3) ≤
      2 ^ ((n - 2 * d) - 3) := by
    exact Nat.pow_le_pow_right (by omega) hexp
  have hbudget : n * 2 ^ (commonFaceDim a b u x - 3) ≤
      n * 2 ^ ((n - 2 * d) - 3) := Nat.mul_le_mul_left n hpow
  let B := n * 2 ^ (commonFaceDim a b u x - 3)
  let L := n * 2 ^ ((n - 2 * d) - 3)
  let wp : ℕ → EuclideanSpace ℝ (Fin d) := fun j => w (min j B)
  refine ⟨wp, ?_, ?_, ?_⟩
  · simpa [wp, B] using hw0
  · have hmin : min L B = B := Nat.min_eq_right hbudget
    simpa [wp, L, B, hmin] using hwD
  · intro j hj
    by_cases hjB : j < B
    · have hjle : j ≤ B := Nat.le_of_lt hjB
      have hsuccle : j + 1 ≤ B := by omega
      simpa [wp, Nat.min_eq_left hjle, Nat.min_eq_left hsuccle] using hwstep j hjB
    · have hBj : B ≤ j := by omega
      have hBsucc : B ≤ j + 1 := by omega
      exact Or.inl (by simp [wp, Nat.min_eq_right hBj, Nat.min_eq_right hBsucc])

end HirschPolynomialAccess
