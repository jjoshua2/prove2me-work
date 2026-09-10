import Mathlib
import Solutions.PolynomialLocalNeutralRank

open scoped RealInnerProductSpace
open Set Hirsch HirschPolynomialAccess

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschPrescribed

/-- Shared active normals may be quotiented out before measuring new rank.
This can be much smaller than the rank of the newly active normals themselves. -/
theorem common_direction_finrank_le_residual_new_subspace
    (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hnew : ∀ j, a j ≠ 0 → ⟪a j, x⟫ = b j → ⟪a j, u⟫ ≠ b j →
      a j ∈ K ⊔ Submodule.span ℝ
        (a '' {i | ⟪a i, u⟫ = b i ∧ ⟪a i, x⟫ = b i})) :
    commonFaceDim a b u x ≤ Module.finrank ℝ K := by
  classical
  let W := commonDirection a b u x
  let C := Submodule.span ℝ (a '' {i | ⟪a i, u⟫ = b i ∧ ⟪a i, x⟫ = b i})
  let T : W →ₗ[ℝ] (K →ₗ[ℝ] ℝ) :=
    { toFun := fun q =>
        { toFun := fun k =>
            ⟪(k : EuclideanSpace ℝ (Fin d)), (q : EuclideanSpace ℝ (Fin d))⟫
          map_add' := by intro k l; simp [inner_add_left]
          map_smul' := by intro t k; simp [inner_smul_left] }
      map_add' := by intro p q; ext k; simp [inner_add_right]
      map_smul' := by intro t q; ext k; simp [inner_smul_right] }
  have hTinj : Function.Injective T := by
    intro y z hyz
    apply Subtype.ext
    let q : W := y - z
    have hTq : T q = 0 := by
      change T (y - z) = 0
      rw [map_sub, hyz, sub_self]
    let A : Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
      { carrier := {k | ⟪k, (q : EuclideanSpace ℝ (Fin d))⟫ = 0}
        zero_mem' := by
          change ⟪(0 : EuclideanSpace ℝ (Fin d)), (q : EuclideanSpace ℝ (Fin d))⟫ = 0
          exact inner_zero_left _
        add_mem' := by
          intro k l hk hl
          change ⟪k + l, (q : EuclideanSpace ℝ (Fin d))⟫ = 0
          rw [inner_add_left, hk, hl, add_zero]
        smul_mem' := by
          intro t k hk
          change ⟪t • k, (q : EuclideanSpace ℝ (Fin d))⟫ = 0
          rw [real_inner_smul_left, hk, mul_zero] }
    have hKA : K ≤ A := by
      intro k hk
      have h := congrArg (fun f : K →ₗ[ℝ] ℝ => f ⟨k, hk⟩) hTq
      exact h
    have hCA : C ≤ A := by
      apply Submodule.span_le.2
      rintro _ ⟨i, hi, rfl⟩
      change ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0
      by_cases hai : a i = 0
      · rw [hai, inner_zero_left]
      have hiC : i ∈ commonSourceRows a b u x := by
        simp [commonSourceRows, hai, hi.1, hi.2]
      have hker : rowEvalMap a (commonSourceRows a b u x)
          (q : EuclideanSpace ℝ (Fin d)) = 0 := LinearMap.mem_ker.1 q.property
      exact congrFun hker ⟨i, hiC⟩
    have hsumA : K ⊔ C ≤ A := sup_le hKA hCA
    have hqTight : ∀ i, ⟪a i, x⟫ = b i →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hix
      by_cases hai : a i = 0
      · rw [hai, inner_zero_left]
      by_cases hiu : ⟪a i, u⟫ = b i
      · exact hCA (Submodule.subset_span ⟨i, ⟨hiu, hix⟩, rfl⟩)
      · exact hsumA (hnew i hai hix hiu)
    have hq0 := vertex_tight_rows_span_checked d n a b x hx
      (q : EuclideanSpace ℝ (Fin d)) hqTight
    change (y : EuclideanSpace ℝ (Fin d)) -
      (z : EuclideanSpace ℝ (Fin d)) = 0 at hq0
    exact sub_eq_zero.mp hq0
  have hle := LinearMap.finrank_le_finrank_of_injective hTinj
  simpa only [Module.finrank_linearMap_self] using hle

#print axioms common_direction_finrank_le_residual_new_subspace

end HirschPrescribed
