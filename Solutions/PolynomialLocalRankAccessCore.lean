import Mathlib
import Solutions.PolynomialLocalNeutralRank
import Solutions.PolynomialCommonFaceTransport
import Solutions.PolynomialAdjEndpoints

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 5000000

noncomputable section

namespace HirschPolynomialAccess

variable {d n : ℕ}

/-- Transport a coordinate-polytope diameter estimate to a walk between two
vertices in their common-source face. All edges remain genuine parent edges. -/
lemma common_face_walk_of_coord_diam
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (B : ℕ)
    (hD : DiamLE (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)) B) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
      w 0 = u ∧ w B = x ∧
      ∀ j < B, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
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
  have hquExt : qu ∈ extremePoints ℝ Q :=
    commonFace_coord_extreme_of_face_extreme a b u x (by simpa [hqu] using huFext)
  have hqxExt : qx ∈ extremePoints ℝ Q :=
    commonFace_coord_extreme_of_face_extreme a b u x (by simpa [hqx] using hxFext)
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
    · exact Or.inl (congrArg (commonFacePoint a b u x) heq)
    · exact Or.inr (commonFace_coord_adj_to_parent a b u x hadj)

/-- A predicate first attained along a padded walk is attained across a
genuine edge. No diameter estimate is involved in this graph lemma. -/
lemma localRank_first_hit_edge
    {E : Type*} (R : E → E → Prop) (T : E → Prop)
    {B : ℕ} (w : ℕ → E)
    (h0 : ¬ T (w 0)) (hB : T (w B))
    (hstep : ∀ j < B, w j = w (j + 1) ∨ R (w j) (w (j + 1))) :
    ∃ j < B, ¬ T (w j) ∧ T (w (j + 1)) ∧ R (w j) (w (j + 1)) := by
  classical
  have hex : ∃ k : ℕ, k ≤ B ∧ T (w k) := ⟨B, le_rfl, hB⟩
  let k := Nat.find hex
  have hk : k ≤ B ∧ T (w k) := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h
    apply h0
    simpa [h] using hk.2
  obtain ⟨j, hjk⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hjB : j < B := by omega
  have hjnot : ¬ T (w j) := by
    intro hjT
    have hmin : k ≤ j := Nat.find_min' hex ⟨by omega, hjT⟩
    omega
  have hjnext : T (w (j + 1)) := by simpa [hjk] using hk.2
  have hadj : R (w j) (w (j + 1)) := by
    rcases hstep j hjB with heq | hadj
    · exact False.elim (hjnot (heq ▸ hjnext))
    · exact hadj
  exact ⟨j, hjB, hjnot, hjnext, hadj⟩

/-- The geometric shortening theorem, independent of any conjectural or
imported diameter theorem. Supply connectivity and any uniform diameter
budget `B` in dimensions at most `r`. A rank-at-most-`r` subspace may be chosen
separately at each target-avoiding vertex and need contain only its active
neutral normals. The conclusion is access to SOME target supporting row,
not a prescribed row or the target vertex. -/
theorem target_face_access_of_local_neutral_rank_core
    (d n r B : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (huv : u ≠ v)
    (hlocal : ∀ x ∈ extremePoints ℝ (Hpoly a b),
      (∀ i, a i ≠ 0 → ⟪a i, v⟫ = b i → ⟪a i, x⟫ ≠ b i) →
      ∃ K : Submodule ℝ (EuclideanSpace ℝ (Fin d)),
        Module.finrank ℝ K ≤ r ∧
        ∀ i, a i ≠ 0 → ⟪a i, u⟫ ≠ b i → ⟪a i, v⟫ ≠ b i →
          ⟪a i, x⟫ = b i → a i ∈ K)
    (hconnect : ∃ D : ℕ, ∃ wg : ℕ → EuclideanSpace ℝ (Fin d),
      wg 0 = u ∧ wg D = v ∧
      ∀ j < D, wg j = wg (j + 1) ∨ Adj (Hpoly a b) (wg j) (wg (j + 1)))
    (hlow : ∀ (e : ℕ), e ≤ r →
      ∀ (a' : Fin n → EuclideanSpace ℝ (Fin e)) (b' : Fin n → ℝ),
        (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
        DiamLE (Hpoly a' b') B) :
    ∃ (i : Fin n) (z : EuclideanSpace ℝ (Fin d)),
      a i ≠ 0 ∧ ⟪a i, v⟫ = b i ∧
      z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (B + 1) = z ∧
        ∀ j < B + 1,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  classical
  let P := Hpoly a b
  let T : EuclideanSpace ℝ (Fin d) → Prop := fun y =>
    ∃ i : Fin n, a i ≠ 0 ∧ ⟪a i, v⟫ = b i ∧ ⟪a i, y⟫ = b i
  by_cases hTu : T u
  · obtain ⟨i, hai, hiv, hiu⟩ := hTu
    exact ⟨i, u, hai, hiv, hu, hiu, (fun _ => u), rfl, rfl,
      fun _ _ => Or.inl rfl⟩
  have hexTarget : ∃ i : Fin n, a i ≠ 0 ∧ ⟪a i, v⟫ = b i := by
    by_contra hn
    have horth : ∀ i, ⟪a i, v⟫ = b i → ⟪a i, u - v⟫ = 0 := by
      intro i hit
      have hai : a i = 0 := by
        by_contra hne
        exact hn ⟨i, hne, hit⟩
      rw [hai, inner_zero_left]
    have hdiff := vertex_tight_rows_span_checked d n a b v hv (u - v) horth
    exact huv (sub_eq_zero.mp hdiff)
  obtain ⟨it, hait, hitv⟩ := hexTarget
  have hTv : T v := ⟨it, hait, hitv, hitv⟩
  obtain ⟨D, wg, hwg0, hwgD, hwgstep⟩ := hconnect
  have hTstart : ¬ T (wg 0) := by simpa only [hwg0] using hTu
  have hTend : T (wg D) := by simpa only [hwgD] using hTv
  obtain ⟨j, hjD, hxavoid, hztarget, hxz⟩ :=
    localRank_first_hit_edge (Adj P) T wg hTstart hTend hwgstep
  let x := wg j
  let z := wg (j + 1)
  have hxz' : Adj P x z := hxz
  have hxext : x ∈ extremePoints ℝ P := adj_left_extreme P hxz'
  have hzext : z ∈ extremePoints ℝ P := adj_right_extreme P hxz'
  have hxavoid' : ∀ i, a i ≠ 0 → ⟪a i, v⟫ = b i → ⟪a i, x⟫ ≠ b i := by
    intro i hai hiv hix
    exact hxavoid ⟨i, hai, hiv, hix⟩
  obtain ⟨K, hKr, hK⟩ := hlocal x hxext hxavoid'
  have hdim : commonFaceDim a b u x ≤ r :=
    (common_face_dim_le_active_neutral_subspace a b u v x hxext hxavoid' K hK).trans hKr
  have hQne : (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)).Nonempty := by
    obtain ⟨q, hq, _⟩ := commonFacePoint_surjOn a b u x
      (commonFace_u_mem a b u x hu.1)
    exact ⟨q, hq⟩
  have hD : DiamLE (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)) B :=
    hlow _ hdim _ _ hQne (commonFace_coord_bounded a b u x hbd)
  obtain ⟨w0, hw00, hw0x, hw0step⟩ :=
    common_face_walk_of_coord_diam a b u x hu hxext B hD
  obtain ⟨i, hai, hiv, hiz⟩ := hztarget
  let w : ℕ → EuclideanSpace ℝ (Fin d) := fun k => if k ≤ B then w0 k else z
  refine ⟨i, z, hai, hiv, hzext, hiz, w, ?_, ?_, ?_⟩
  · change (if 0 ≤ B then w0 0 else z) = u
    rw [if_pos (Nat.zero_le B)]
    exact hw00
  · change (if B + 1 ≤ B then w0 (B + 1) else z) = z
    exact if_neg (by omega)
  · intro k hk
    by_cases hkB : k < B
    · have hk0 : k ≤ B := by omega
      have hk1 : k + 1 ≤ B := by omega
      simpa only [w, if_pos hk0, if_pos hk1] using hw0step k hkB
    · have hkeq : k = B := by omega
      subst k
      have hleft : w B = x := by
        change (if B ≤ B then w0 B else z) = x
        rw [if_pos le_rfl]
        exact hw0x
      have hright : w (B + 1) = z := by
        change (if B + 1 ≤ B then w0 (B + 1) else z) = z
        exact if_neg (by omega)
      exact Or.inr (by simpa only [hleft, hright] using hxz')

#print axioms target_face_access_of_local_neutral_rank_core

end HirschPolynomialAccess
