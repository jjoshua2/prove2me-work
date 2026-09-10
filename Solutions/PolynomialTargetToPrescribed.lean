import Mathlib
import Definitions.Def_Hirsch_model
import Solutions.PolynomialTargetFaceDiameterBridge
import Solutions.PolynomialProductWalk

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 6000000

noncomputable section

namespace HirschPolynomialAccess

variable {d n : ℕ}

/-- A row that is tight at both endpoints of a common face restricts to the
zero normal in common-face coordinates. -/
lemma commonFaceA_eq_zero_of_tight_both
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) (i : Fin n)
    (hiu : ⟪a i, u⟫ = b i) (hix : ⟪a i, x⟫ = b i) :
    commonFaceA a b u x i = 0 := by
  by_cases hai : a i = 0
  · simp [commonFaceA, hai]
  · apply inner_self_eq_zero.mp
    rw [commonFace_inner_restricted]
    have hiC : i ∈ commonSourceRows a b u x := by
      simp [commonSourceRows, hai, hiu, hix]
    have hlift := commonFaceLift_mem_direction a b u x (commonFaceA a b u x i)
    have hker : rowEvalMap a (commonSourceRows a b u x)
        (commonFaceLift a b u x (commonFaceA a b u x i)) = 0 :=
      LinearMap.mem_ker.1 hlift
    change (rowEvalMap a (commonSourceRows a b u x)
      (commonFaceLift a b u x (commonFaceA a b u x i))) ⟨i, hiC⟩ = 0
    exact congrFun hker ⟨i, hiC⟩

/-- Tightness of an original row is exactly tightness of its common-face
coordinate inequality at a coordinate point representing that original point. -/
lemma commonFace_coord_row_eq_of_point_eq
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x y : EuclideanSpace ℝ (Fin d))
    (q : EuclideanSpace ℝ (Fin (commonFaceDim a b u x)))
    (i : Fin n)
    (hpoint : commonFacePoint a b u x q = y)
    (hiy : ⟪a i, y⟫ = b i) :
    ⟪commonFaceA a b u x i, q⟫ = commonFaceB a b u x i := by
  rw [commonFace_inner_restricted]
  dsimp [commonFaceB]
  have h := hiy
  rw [← hpoint] at h
  dsimp [commonFacePoint] at h
  rw [inner_add_right] at h
  linarith

lemma commonFace_parent_row_eq_of_coord
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x y : EuclideanSpace ℝ (Fin d))
    (q : EuclideanSpace ℝ (Fin (commonFaceDim a b u x)))
    (i : Fin n)
    (hpoint : commonFacePoint a b u x q = y)
    (hqi : ⟪commonFaceA a b u x i, q⟫ = commonFaceB a b u x i) :
    ⟪a i, y⟫ = b i := by
  rw [commonFace_inner_restricted] at hqi
  dsimp [commonFaceB] at hqi
  rw [← hpoint]
  dsimp [commonFacePoint]
  rw [inner_add_right]
  linarith

/-- In the coordinate model of the full common face of `u,x`, the coordinate
images of the two endpoints are separated by every nonzero coordinate row.
Any row tight at both original endpoints has already become a zero row. -/
lemma commonFace_coord_endpoints_separated
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (qx : EuclideanSpace ℝ (Fin (commonFaceDim a b u x)))
    (hqx : commonFacePoint a b u x qx = x) :
    ∀ i, commonFaceA a b u x i ≠ 0 →
      ⟪commonFaceA a b u x i, 0⟫ ≠ commonFaceB a b u x i ∨
      ⟪commonFaceA a b u x i, qx⟫ ≠ commonFaceB a b u x i := by
  intro i hAi
  by_cases h0 : ⟪commonFaceA a b u x i, 0⟫ = commonFaceB a b u x i
  · right
    intro hq
    have hpoint0 : commonFacePoint a b u x 0 = u := by simp [commonFacePoint]
    have hiu := commonFace_parent_row_eq_of_coord a b u x u 0 i hpoint0 h0
    have hix := commonFace_parent_row_eq_of_coord a b u x x qx i hqx hq
    exact hAi (commonFaceA_eq_zero_of_tight_both a b u x i hiu hix)
  · exact Or.inl h0

end HirschPolynomialAccess

namespace Hirsch

open HirschPolynomialAccess

/-- Uniform polynomial access to some supporting face of the target vertex
implies access to any prescribed supporting face, losing only one factor of
ambient dimension.

After one existential target-face step reaches `z`, either `z` is already on
the requested row, or `z` and the target `v` share the newly reached nonzero
row.  Their full common face is therefore lower-dimensional.  In its exact
coordinate model all rows tight at both endpoints restrict to zero, so the two
coordinate endpoints satisfy the separation hypothesis automatically; recurse
there on the prescribed row. -/
theorem prescribed_face_access_of_target_face_access_verified (C k : ℕ)
    (haccess : ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hpoly a b) →
      ∀ u ∈ extremePoints ℝ (Hpoly a b),
      ∀ v ∈ extremePoints ℝ (Hpoly a b), u ≠ v →
      (∀ i, a i ≠ 0 → ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i) →
      ∃ (i : Fin n) (z : EuclideanSpace ℝ (Fin d)),
        a i ≠ 0 ∧ ⟪a i, v⟫ = b i ∧
        z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
        ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
          w 0 = u ∧ w (C * (n + d) ^ k) = z ∧
          ∀ j < C * (n + d) ^ k,
            w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1))) :
    ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hpoly a b) →
      ∀ u ∈ extremePoints ℝ (Hpoly a b),
      ∀ v ∈ extremePoints ℝ (Hpoly a b), u ≠ v →
      (∀ j, a j ≠ 0 → ⟪a j, u⟫ ≠ b j ∨ ⟪a j, v⟫ ≠ b j) →
      ∀ i : Fin n, a i ≠ 0 → ⟪a i, v⟫ = b i →
      ∃ z : EuclideanSpace ℝ (Fin d),
        z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
        ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
          w 0 = u ∧ w (d * C * (n + d) ^ k) = z ∧
          ∀ j < d * C * (n + d) ^ k,
            w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro n a b hbd u hu v hv huv hsep i hai hiv
      let L : ℕ := C * (n + d) ^ k
      have hdpos : 0 < d := by
        by_contra hd
        have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
        subst d
        exact hai (Subsingleton.elim _ _)
      obtain ⟨j, z, haj, hjv, hz, hjz, p, hp0, hpLraw, hpstepraw⟩ :=
        haccess d n a b hbd u hu v hv huv hsep
      have hpL : p L = z := by simpa [L] using hpLraw
      have hpstep : ∀ t < L,
          p t = p (t + 1) ∨ Adj (Hpoly a b) (p t) (p (t + 1)) := by
        simpa [L] using hpstepraw
      by_cases hzi : ⟪a i, z⟫ = b i
      · have hbudget : L ≤ d * L := by
          have : 1 ≤ d := hdpos
          simpa [one_mul] using Nat.mul_le_mul_right L this
        obtain ⟨p', hp'0, hp'B, hp'step⟩ :=
          HirschProduct.pad_walk (Adj (Hpoly a b)) hbudget p hp0 hpL hpstep
        refine ⟨z, hz, hzi, p', hp'0, ?_, ?_⟩
        · simpa [L, Nat.mul_assoc] using hp'B
        · intro t ht
          have ht' : t < d * L := by simpa [L, Nat.mul_assoc] using ht
          exact hp'step t ht'
      · let e : ℕ := commonFaceDim a b z v
        have hed : e < d := by
          dsimp [e]
          exact commonFaceDim_lt_of_shared_nonzero_row a b z v j haj hjz hjv
        let aF := commonFaceA a b z v
        let bF := commonFaceB a b z v
        let Q := Hpoly aF bF
        have hzF : z ∈ commonFace a b z v := commonFace_u_mem a b z v hz.1
        have hvF : v ∈ commonFace a b z v := commonFace_x_mem a b z v hv.1
        have hzFext : z ∈ extremePoints ℝ (commonFace a b z v) := by
          rw [(commonFace_isExtreme a b z v).extremePoints_eq]
          exact ⟨hzF, hz⟩
        have hvFext : v ∈ extremePoints ℝ (commonFace a b z v) := by
          rw [(commonFace_isExtreme a b z v).extremePoints_eq]
          exact ⟨hvF, hv⟩
        have hq0ext : (0 : EuclideanSpace ℝ (Fin e)) ∈ extremePoints ℝ Q := by
          dsimp [e, Q, aF, bF]
          apply commonFace_coord_extreme_of_face_extreme a b z v
          simpa [commonFacePoint] using hzFext
        obtain ⟨qv, hqvQ, hqvpt⟩ := commonFacePoint_surjOn a b z v hvF
        have hqvext : qv ∈ extremePoints ℝ Q := by
          dsimp [Q, aF, bF]
          apply commonFace_coord_extreme_of_face_extreme a b z v
          simpa [hqvpt] using hvFext
        have hqvi : ⟪aF i, qv⟫ = bF i := by
          dsimp [aF, bF]
          exact commonFace_coord_row_eq_of_point_eq a b z v v qv i hqvpt hiv
        have haiF : aF i ≠ 0 := by
          intro hAi
          have hzero : (0 : ℝ) = bF i := by
            simpa [hAi] using hqvi
          apply hzi
          dsimp [bF, commonFaceB] at hzero
          linarith
        have hqne : (0 : EuclideanSpace ℝ (Fin e)) ≠ qv := by
          intro h0v
          apply hzi
          have hzv : z = v := by
            calc
              z = commonFacePoint a b z v 0 := by simp [commonFacePoint]
              _ = commonFacePoint a b z v qv := by rw [h0v]
              _ = v := hqvpt
          rw [hzv]
          exact hiv
        have hsepF : ∀ t, aF t ≠ 0 →
            ⟪aF t, (0 : EuclideanSpace ℝ (Fin e))⟫ ≠ bF t ∨
            ⟪aF t, qv⟫ ≠ bF t := by
          dsimp [aF, bF]
          exact commonFace_coord_endpoints_separated a b z v qv hqvpt
        have hFbd : Bornology.IsBounded Q := by
          dsimp [Q, aF, bF]
          exact commonFace_coord_bounded a b z v hbd
        obtain ⟨qy, hqy, hqyi, r, hr0, hrB, hrstep⟩ :=
          ih e hed n aF bF hFbd 0 hq0ext qv hqvext hqne hsepF i haiF hqvi
        let Brec : ℕ := e * C * (n + e) ^ k
        have hrB' : r Brec = qy := by simpa [Brec] using hrB
        have hrstep' : ∀ t < Brec,
            r t = r (t + 1) ∨ Adj Q (r t) (r (t + 1)) := by
          simpa [Brec] using hrstep
        let y := commonFacePoint a b z v qy
        have hy : y ∈ extremePoints ℝ (Hpoly a b) := by
          apply commonFace_extremePoints_subset_parent a b z v
          apply commonFace_face_extreme_of_coord_extreme a b z v
          simpa [Q, aF, bF] using hqy
        have hyi : ⟪a i, y⟫ = b i := by
          apply commonFace_parent_row_eq_of_coord a b z v y qy i rfl
          simpa [aF, bF] using hqyi
        let rP : ℕ → EuclideanSpace ℝ (Fin d) :=
          fun t => commonFacePoint a b z v (r t)
        have hrP0 : rP 0 = z := by
          dsimp [rP]
          rw [hr0]
          simp [commonFacePoint]
        have hrPB : rP Brec = y := by
          dsimp [rP, y]
          rw [hrB']
        have hrPstep : ∀ t < Brec,
            rP t = rP (t + 1) ∨ Adj (Hpoly a b) (rP t) (rP (t + 1)) := by
          intro t ht
          rcases hrstep' t ht with heq | hadj
          · exact Or.inl (by
              simpa [rP] using congrArg (commonFacePoint a b z v) heq)
          · exact Or.inr (by
              simpa [rP, Q, aF, bF] using
                commonFace_coord_adj_to_parent a b z v hadj)
        have hepred : e ≤ d - 1 := by omega
        have hbase : n + e ≤ n + d := by omega
        have htail : Brec ≤ (d - 1) * L := by
          dsimp [Brec, L]
          calc
            e * C * (n + e) ^ k ≤ (d - 1) * C * (n + e) ^ k := by gcongr
            _ ≤ (d - 1) * C * (n + d) ^ k := by gcongr
            _ = (d - 1) * (C * (n + d) ^ k) := by ring
        obtain ⟨rP', hrP'0, hrP'tail, hrP'step⟩ :=
          HirschProduct.pad_walk (Adj (Hpoly a b)) htail
            rP hrP0 hrPB hrPstep
        obtain ⟨w, hw0, hwlen, hwstep⟩ :=
          HirschProduct.append_walk (Adj (Hpoly a b)) p rP'
            hp0 hpL hrP'0 hrP'tail hpstep hrP'step
        have hddec : 1 + (d - 1) = d := by omega
        have hlen : L + (d - 1) * L = d * L := by
          calc
            L + (d - 1) * L = (1 + (d - 1)) * L := by ring
            _ = d * L := by rw [hddec]
        refine ⟨y, hy, hyi, w, hw0, ?_, ?_⟩
        · have : w (d * L) = y := by
            rw [← hlen]
            exact hwlen
          simpa [L, Nat.mul_assoc] using this
        · intro t ht
          have ht' : t < d * L := by simpa [L, Nat.mul_assoc] using ht
          have : t < L + (d - 1) * L := by simpa [hlen] using ht'
          exact hwstep t this

/-- Hence the existential polynomial target-face theorem and the prescribed
supporting-face theorem differ by at most one exponent in `n+d`. -/
theorem polynomial_prescribed_face_access_of_target_face_access
    (haccess : ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hpoly a b) →
      ∀ u ∈ extremePoints ℝ (Hpoly a b),
      ∀ v ∈ extremePoints ℝ (Hpoly a b), u ≠ v →
      (∀ i, a i ≠ 0 → ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i) →
      ∃ (i : Fin n) (z : EuclideanSpace ℝ (Fin d)),
        a i ≠ 0 ∧ ⟪a i, v⟫ = b i ∧
        z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
        ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
          w 0 = u ∧ w (C * (n + d) ^ k) = z ∧
          ∀ j < C * (n + d) ^ k,
            w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1))) :
    ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hpoly a b) →
      ∀ u ∈ extremePoints ℝ (Hpoly a b),
      ∀ v ∈ extremePoints ℝ (Hpoly a b), u ≠ v →
      (∀ j, a j ≠ 0 → ⟪a j, u⟫ ≠ b j ∨ ⟪a j, v⟫ ≠ b j) →
      ∀ i : Fin n, a i ≠ 0 → ⟪a i, v⟫ = b i →
      ∃ z : EuclideanSpace ℝ (Fin d),
        z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
        ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
          w 0 = u ∧ w (C * (n + d) ^ k) = z ∧
          ∀ j < C * (n + d) ^ k,
            w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  obtain ⟨C, k, haccess⟩ := haccess
  refine ⟨C, k + 1, ?_⟩
  intro d n a b hbd u hu v hv huv hsep i hai hiv
  obtain ⟨z, hz, hiz, w, hw0, hwB, hwstep⟩ :=
    prescribed_face_access_of_target_face_access_verified C k haccess
      d n a b hbd u hu v hv huv hsep i hai hiv
  have hdN : d ≤ n + d := by omega
  have hbudget : d * C * (n + d) ^ k ≤ C * (n + d) ^ (k + 1) := by
    calc
      d * C * (n + d) ^ k = d * (C * (n + d) ^ k) := by ring
      _ ≤ (n + d) * (C * (n + d) ^ k) :=
        Nat.mul_le_mul_right (C * (n + d) ^ k) hdN
      _ = C * (n + d) ^ (k + 1) := by
        rw [pow_succ]
        ring
  obtain ⟨w', hw'0, hw'B, hw'step⟩ :=
    HirschProduct.pad_walk (Adj (Hpoly a b)) hbudget w hw0 hwB hwstep
  exact ⟨z, hz, hiz, w', hw'0, hw'B, hw'step⟩

#print axioms HirschPolynomialAccess.commonFaceA_eq_zero_of_tight_both
#print axioms HirschPolynomialAccess.commonFace_coord_row_eq_of_point_eq
#print axioms HirschPolynomialAccess.commonFace_parent_row_eq_of_coord
#print axioms HirschPolynomialAccess.commonFace_coord_endpoints_separated
#print axioms prescribed_face_access_of_target_face_access_verified
#print axioms polynomial_prescribed_face_access_of_target_face_access

end Hirsch
