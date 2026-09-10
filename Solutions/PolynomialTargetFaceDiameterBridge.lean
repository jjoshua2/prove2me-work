import Mathlib
import Definitions.Def_Hirsch_model
import Solutions.PolynomialProductWalk
import Solutions.PolynomialCommonFaceTransport

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 5000000

noncomputable section

namespace HirschPolynomialAccess

variable {d n : ℕ}

/-- A diameter bound in the coordinate model of the common supporting face of
`u,x` transports to a genuine parent-polytope edge walk between `u` and `x`. -/
lemma common_face_walk_of_diamLE
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    {B : ℕ}
    (hD : DiamLE
      (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)) B) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
      w 0 = u ∧ w B = x ∧
      ∀ j < B,
        w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  let Q := Hpoly (commonFaceA a b u x) (commonFaceB a b u x)
  have huF : u ∈ commonFace a b u x := commonFace_u_mem a b u x hu.1
  have hxF : x ∈ commonFace a b u x := commonFace_x_mem a b u x hx.1
  have huFext : u ∈ extremePoints ℝ (commonFace a b u x) := by
    rw [(commonFace_isExtreme a b u x).extremePoints_eq]
    exact ⟨huF, hu⟩
  have hxFext : x ∈ extremePoints ℝ (commonFace a b u x) := by
    rw [(commonFace_isExtreme a b u x).extremePoints_eq]
    exact ⟨hxF, hx⟩
  obtain ⟨qu, hquQ, hqu⟩ := commonFacePoint_surjOn a b u x huF
  obtain ⟨qx, hqxQ, hqx⟩ := commonFacePoint_surjOn a b u x hxF
  have hquExt : qu ∈ extremePoints ℝ Q := by
    apply commonFace_coord_extreme_of_face_extreme a b u x
    simpa [hqu] using huFext
  have hqxExt : qx ∈ extremePoints ℝ Q := by
    apply commonFace_coord_extreme_of_face_extreme a b u x
    simpa [hqx] using hxFext
  obtain ⟨wq, hwq0, hwqB, hwqstep⟩ := hD qu hquExt qx hqxExt
  let w : ℕ → EuclideanSpace ℝ (Fin d) :=
    fun j => commonFacePoint a b u x (wq j)
  refine ⟨w, ?_, ?_, ?_⟩
  · dsimp [w]
    rw [hwq0, hqu]
  · dsimp [w]
    rw [hwqB, hqx]
  · intro j hj
    rcases hwqstep j hj with heq | hadj
    · exact Or.inl (by
        simpa [w] using congrArg (commonFacePoint a b u x) heq)
    · exact Or.inr (by
        simpa [w] using commonFace_coord_adj_to_parent a b u x hadj)

/-- A single nonzero row active at both endpoints makes their common supporting
face genuinely lower-dimensional. -/
lemma commonFaceDim_lt_of_shared_nonzero_row
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) (i : Fin n)
    (hai : a i ≠ 0)
    (hiu : ⟪a i, u⟫ = b i) (hix : ⟪a i, x⟫ = b i) :
    commonFaceDim a b u x < d := by
  classical
  have hiC : i ∈ commonSourceRows a b u x := by
    simp [commonSourceRows, hai, hiu, hix]
  have hproper : commonDirection a b u x < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    have hai_mem : a i ∈ commonDirection a b u x := by
      rw [htop]
      exact Submodule.mem_top
    have hker := LinearMap.mem_ker.mp hai_mem
    have hself : ⟪a i, a i⟫ = 0 := by
      change (rowEvalMap a (commonSourceRows a b u x) (a i)) ⟨i, hiC⟩ = 0
      exact congrFun hker ⟨i, hiC⟩
    exact hai (inner_self_eq_zero.mp hself)
  have hfin := Submodule.finrank_lt_finrank_of_lt hproper
  simpa [commonFaceDim] using hfin

end HirschPolynomialAccess

namespace Hirsch

open HirschPolynomialAccess

/-- A polynomial target-face access bound implies a global diameter bound with
only one factor of the ambient dimension.

The proof uses strong induction on `d`.  If the endpoints already share a
nonzero supporting row, they lie in a proper common face and we recurse there.
Otherwise the access hypothesis spends one `C*(n+d)^k` block to reach a vertex
on a nonzero target supporting face; that new vertex and the target then share
that row, so the remaining route lies in dimension `< d`. -/
theorem diameter_bound_of_target_face_access_verified (C k : ℕ)
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
    ∀ (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hpoly a b) →
      DiamLE (Hpoly a b) (d * C * (n + d) ^ k) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro n a b hbd u hu v hv
      let L : ℕ := C * (n + d) ^ k
      by_cases huv : u = v
      · subst v
        refine ⟨fun _ => u, rfl, ?_, ?_⟩
        · rfl
        · intro j hj
          exact Or.inl rfl
      by_cases hsep : ∀ i, a i ≠ 0 →
          ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i
      · obtain ⟨i, z, hai, hiv, hz, hiz, p, hp0, hpL, hpstep⟩ :=
          haccess d n a b hbd u hu v hv huv hsep
        let e : ℕ := commonFaceDim a b z v
        have hed : e < d := by
          dsimp [e]
          exact commonFaceDim_lt_of_shared_nonzero_row a b z v i hai hiz hiv
        let aF := commonFaceA a b z v
        let bF := commonFaceB a b z v
        have hFbd : Bornology.IsBounded (Hpoly aF bF) := by
          dsimp [aF, bF]
          exact commonFace_coord_bounded a b z v hbd
        have hFD : DiamLE (Hpoly aF bF) (e * C * (n + e) ^ k) := by
          exact ih e hed n aF bF hFbd
        obtain ⟨q, hq0, hqB, hqstep⟩ :=
          common_face_walk_of_diamLE a b z v hz hv hFD
        have hepred : e ≤ d - 1 := by omega
        have hbase : n + e ≤ n + d := by omega
        have htail : e * C * (n + e) ^ k ≤ (d - 1) * L := by
          dsimp [L]
          calc
            e * C * (n + e) ^ k ≤ (d - 1) * C * (n + e) ^ k := by gcongr
            _ ≤ (d - 1) * C * (n + d) ^ k := by gcongr
            _ = (d - 1) * (C * (n + d) ^ k) := by
              simp [Nat.mul_assoc]
        obtain ⟨q', hq'0, hq'tail, hq'step⟩ :=
          HirschProduct.pad_walk (Adj (Hpoly a b)) htail
            q hq0 hqB hqstep
        obtain ⟨w, hw0, hwB, hwstep⟩ :=
          HirschProduct.append_walk (Adj (Hpoly a b)) p q'
            hp0 hpL hq'0 hq'tail hpstep hq'step
        have hdpos : 0 < d := by omega
        have hddec : 1 + (d - 1) = d := by omega
        have hlen : L + (d - 1) * L = d * L := by
          calc
            L + (d - 1) * L = (1 + (d - 1)) * L := by
              rw [add_mul, one_mul]
            _ = d * L := by rw [hddec]
        refine ⟨w, hw0, ?_, ?_⟩
        · have hwB' : w (d * L) = v := by simpa [hlen] using hwB
          simpa [L, Nat.mul_assoc] using hwB'
        · intro j hj
          have hj' : j < d * L := by
            simpa [L, Nat.mul_assoc] using hj
          have := hwstep j (by simpa [hlen] using hj')
          exact this
      · simp only [not_forall, not_imp, not_or, not_not] at hsep
        obtain ⟨i, hai, hiu, hiv⟩ := hsep
        let e : ℕ := commonFaceDim a b u v
        have hed : e < d := by
          dsimp [e]
          exact commonFaceDim_lt_of_shared_nonzero_row a b u v i hai hiu hiv
        let aF := commonFaceA a b u v
        let bF := commonFaceB a b u v
        have hFbd : Bornology.IsBounded (Hpoly aF bF) := by
          dsimp [aF, bF]
          exact commonFace_coord_bounded a b u v hbd
        have hFD : DiamLE (Hpoly aF bF) (e * C * (n + e) ^ k) := by
          exact ih e hed n aF bF hFbd
        obtain ⟨q, hq0, hqB, hqstep⟩ :=
          common_face_walk_of_diamLE a b u v hu hv hFD
        have he_le : e ≤ d := Nat.le_of_lt hed
        have hbase : n + e ≤ n + d := by omega
        have hbudget : e * C * (n + e) ^ k ≤ d * C * (n + d) ^ k := by
          calc
            e * C * (n + e) ^ k ≤ d * C * (n + e) ^ k := by gcongr
            _ ≤ d * C * (n + d) ^ k := by gcongr
        exact HirschProduct.pad_walk (Adj (Hpoly a b)) hbudget
          q hq0 hqB hqstep

#print axioms HirschPolynomialAccess.common_face_walk_of_diamLE
#print axioms HirschPolynomialAccess.commonFaceDim_lt_of_shared_nonzero_row
#print axioms diameter_bound_of_target_face_access_verified

end Hirsch
