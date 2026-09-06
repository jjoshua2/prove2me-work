import Mathlib
import Solutions.PolynomialCommonFaceCoords

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 3000000

noncomputable section

namespace HirschPolynomialAccess

variable {d n : ℕ}

/-- Only the normals newly active at `x`, not all neutral normals in the
whole description, are needed to bound the common-source direction space.
No separation or extremality assumption on `u` is needed. -/
theorem common_direction_finrank_le_new_active_subspace
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hnew : ∀ i, a i ≠ 0 → ⟪a i, x⟫ = b i →
      ⟪a i, u⟫ ≠ b i → a i ∈ K) :
    Module.finrank ℝ (commonDirection a b u x) ≤ Module.finrank ℝ K := by
  classical
  let W := commonDirection a b u x
  let T : W →ₗ[ℝ] (K →ₗ[ℝ] ℝ) :=
    { toFun := fun q =>
        { toFun := fun k =>
            ⟪(k : EuclideanSpace ℝ (Fin d)), (q : EuclideanSpace ℝ (Fin d))⟫
          map_add' := by
            intro k l
            simp [inner_add_left]
          map_smul' := by
            intro t k
            simp [inner_smul_left] }
      map_add' := by
        intro p q
        ext k
        simp [inner_add_right]
      map_smul' := by
        intro t q
        ext k
        simp [inner_smul_right] }
  have hTinj : Function.Injective T := by
    intro y z hyz
    apply Subtype.ext
    let q : W := y - z
    have hTq : T q = 0 := by
      change T (y - z) = 0
      rw [map_sub, hyz, sub_self]
    have hqK : ∀ k : K,
        ⟪(k : EuclideanSpace ℝ (Fin d)), (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro k
      have h := congrArg (fun f : K →ₗ[ℝ] ℝ => f k) hTq
      exact h
    have hqCommon : ∀ i, i ∈ commonSourceRows a b u x →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hi
      have hker : rowEvalMap a (commonSourceRows a b u x)
          (q : EuclideanSpace ℝ (Fin d)) = 0 := LinearMap.mem_ker.1 q.property
      exact congrFun hker ⟨i, hi⟩
    have hqTight : ∀ i, ⟪a i, x⟫ = b i →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hix
      by_cases hai : a i = 0
      · rw [hai, inner_zero_left]
      by_cases hiu : ⟪a i, u⟫ = b i
      · exact hqCommon i (by simp [commonSourceRows, hai, hiu, hix])
      · exact hqK ⟨a i, hnew i hai hix hiu⟩
    have hq0 := vertex_tight_rows_span_checked d n a b x hx
      (q : EuclideanSpace ℝ (Fin d)) hqTight
    change (y : EuclideanSpace ℝ (Fin d)) -
      (z : EuclideanSpace ℝ (Fin d)) = 0 at hq0
    exact sub_eq_zero.mp hq0
  have hle := LinearMap.finrank_le_finrank_of_injective hTinj
  simpa only [Module.finrank_linearMap_self] using hle

/-- At a target-avoiding vertex, a local subspace containing its active
neutral normals controls its common-source face dimension. The subspace may
be different at every vertex. -/
theorem common_face_dim_le_active_neutral_subspace
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (havoid : ∀ i, a i ≠ 0 → ⟪a i, v⟫ = b i → ⟪a i, x⟫ ≠ b i)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hK : ∀ i, a i ≠ 0 → ⟪a i, u⟫ ≠ b i →
      ⟪a i, v⟫ ≠ b i → ⟪a i, x⟫ = b i → a i ∈ K) :
    commonFaceDim a b u x ≤ Module.finrank ℝ K := by
  apply common_direction_finrank_le_new_active_subspace a b u x hx K
  intro i hai hix hiu
  have hiv : ⟪a i, v⟫ ≠ b i := fun h => havoid i hai h hix
  exact hK i hai hiu hiv hix

#print axioms common_direction_finrank_le_new_active_subspace
#print axioms common_face_dim_le_active_neutral_subspace

end HirschPolynomialAccess
