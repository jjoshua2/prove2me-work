import Mathlib
import Solutions.PolynomialLocalRankAccessCore

open scoped RealInnerProductSpace
open Set Hirsch HirschPolynomialAccess

set_option maxHeartbeats 5000000

noncomputable section

namespace HirschPrescribed

/-- A first-contact shortening theorem for an arbitrary designated target set.
Only predecessors of edges entering that set need a rank hypothesis. The
controlled normals are all newly active normals relative to the fixed source,
not just normals neutral relative to a distinguished target vertex.
This geometric core has no imported diameter theorem. -/
theorem target_set_access_of_boundary_new_rank_core
    (d n r B : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (T : EuclideanSpace ℝ (Fin d) → Prop) (hTv : T v)
    (hboundary : ∀ x z, Adj (Hpoly a b) x z → ¬ T x → T z →
      ∃ K : Submodule ℝ (EuclideanSpace ℝ (Fin d)),
        Module.finrank ℝ K ≤ r ∧
        ∀ j, a j ≠ 0 → ⟪a j, x⟫ = b j → ⟪a j, u⟫ ≠ b j → a j ∈ K)
    (hconnect : ∃ D : ℕ, ∃ wg : ℕ → EuclideanSpace ℝ (Fin d),
      wg 0 = u ∧ wg D = v ∧
      ∀ j < D, wg j = wg (j + 1) ∨ Adj (Hpoly a b) (wg j) (wg (j + 1)))
    (hlow : ∀ (e : ℕ), e ≤ r →
      ∀ (a' : Fin n → EuclideanSpace ℝ (Fin e)) (b' : Fin n → ℝ),
        (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
        DiamLE (Hpoly a' b') B) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Hpoly a b) ∧ T z ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (B + 1) = z ∧
        ∀ j < B + 1,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  classical
  by_cases hTu : T u
  · exact ⟨u, hu, hTu, (fun _ => u), rfl, rfl, fun _ _ => Or.inl rfl⟩
  obtain ⟨D, wg, hwg0, hwgD, hwgstep⟩ := hconnect
  have hTstart : ¬ T (wg 0) := by simpa only [hwg0] using hTu
  have hTend : T (wg D) := by simpa only [hwgD] using hTv
  obtain ⟨j, hjD, hxavoid, hztarget, hxz⟩ :=
    localRank_first_hit_edge (Adj (Hpoly a b)) T wg hTstart hTend hwgstep
  let x := wg j
  let z := wg (j + 1)
  have hxz' : Adj (Hpoly a b) x z := hxz
  have hxext : x ∈ extremePoints ℝ (Hpoly a b) := adj_left_extreme _ hxz'
  have hzext : z ∈ extremePoints ℝ (Hpoly a b) := adj_right_extreme _ hxz'
  obtain ⟨K, hKr, hK⟩ := hboundary x z hxz' hxavoid hztarget
  have hdim : commonFaceDim a b u x ≤ r :=
    (common_direction_finrank_le_new_active_subspace a b u x hxext K hK).trans hKr
  have hQne : (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)).Nonempty := by
    obtain ⟨q, hq, _⟩ := commonFacePoint_surjOn a b u x
      (commonFace_u_mem a b u x hu.1)
    exact ⟨q, hq⟩
  have hD : DiamLE (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)) B :=
    hlow _ hdim _ _ hQne (commonFace_coord_bounded a b u x hbd)
  obtain ⟨w0, hw00, hw0x, hw0step⟩ :=
    common_face_walk_of_coord_diam a b u x hu hxext B hD
  let w : ℕ → EuclideanSpace ℝ (Fin d) := fun k => if k ≤ B then w0 k else z
  refine ⟨z, hzext, hztarget, w, ?_, ?_, ?_⟩
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

#print axioms target_set_access_of_boundary_new_rank_core

end HirschPrescribed
