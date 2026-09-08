import Mathlib
import Solutions.PolynomialCommonFaceCoords
import Solutions.PolynomialExcessFaceRank
import Solutions.PolynomialPrescribedFaceCore

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option maxHeartbeats 5000000

noncomputable section

namespace HirschPolynomialAccess

/-- The intersection of the two common-direction spaces at `x` is controlled
by the rows tight at neither endpoint. No separation assumption is needed for
this injectivity statement itself. -/
theorem common_direction_intersection_finrank_le_neutral_card
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b)) :
    Module.finrank ℝ
      (show Submodule ℝ (EuclideanSpace ℝ (Fin d)) from
        commonDirection a b u x ⊓ commonDirection a b v x) ≤
      (neutralRows a b u v).card := by
  classical
  let U : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := commonDirection a b u x
  let V : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := commonDirection a b v x
  let N := neutralRows a b u v
  let W : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := U ⊓ V
  let T : W →ₗ[ℝ] (N → ℝ) := (rowEvalMap a N).domRestrict W
  have hTin : Function.Injective T := by
    intro y z hyz
    apply Subtype.ext
    let q : W := y - z
    have hTq : T q = 0 := by
      change T (y - z) = 0
      rw [map_sub, hyz, sub_self]
    have hqU : ∀ i, i ∈ commonSourceRows a b u x →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hi
      have hker : rowEvalMap a (commonSourceRows a b u x)
          (q : EuclideanSpace ℝ (Fin d)) = 0 := by
        apply LinearMap.mem_ker.1
        exact q.property.1
      exact congrFun hker ⟨i, hi⟩
    have hqV : ∀ i, i ∈ commonSourceRows a b v x →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hi
      have hker : rowEvalMap a (commonSourceRows a b v x)
          (q : EuclideanSpace ℝ (Fin d)) = 0 := by
        apply LinearMap.mem_ker.1
        exact q.property.2
      exact congrFun hker ⟨i, hi⟩
    have hqN : ∀ i, i ∈ N →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hi
      change T q ⟨i, hi⟩ = 0
      exact congrFun hTq ⟨i, hi⟩
    have hqTight : ∀ i, ⟪a i, x⟫ = b i →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hix
      by_cases hai : a i = 0
      · simp [hai]
      by_cases hiu : ⟪a i, u⟫ = b i
      · exact hqU i (by simp [commonSourceRows, hai, hiu, hix])
      by_cases hiv : ⟪a i, v⟫ = b i
      · exact hqV i (by simp [commonSourceRows, hai, hiv, hix])
      · exact hqN i (by simp [N, neutralRows, hai, hiu, hiv])
    have hq0 := vertex_tight_rows_span_checked d n a b x hx
      (q : EuclideanSpace ℝ (Fin d)) hqTight
    change (y : EuclideanSpace ℝ (Fin d)) -
      (z : EuclideanSpace ℝ (Fin d)) = 0 at hq0
    exact sub_eq_zero.mp hq0
  have hle := LinearMap.finrank_le_finrank_of_injective hTin
  simpa [W, U, V, N] using hle

/-- For separated extreme endpoints, the overlap of the source- and
target-common direction spaces costs at most the facet excess `n-2d`. -/
theorem common_direction_intersection_finrank_le_excess
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i) :
    Module.finrank ℝ
      (show Submodule ℝ (EuclideanSpace ℝ (Fin d)) from
        commonDirection a b u x ⊓ commonDirection a b v x) ≤
      n - 2 * d :=
  (common_direction_intersection_finrank_le_neutral_card a b u v x hx).trans
    (neutral_card_le_excess a b u v hu hv hsep)

/-- Two-sided common-face dimension tradeoff for every intermediate vertex of
a separated source/target pair:

`dim F(u,x) + dim F(v,x) ≤ d + (n - 2d)`.

At exact balance `n=2d` this becomes the clean complementary inequality
`dim F(u,x) + dim F(v,x) ≤ d`. -/
theorem commonFaceDim_add_le_dim_add_excess
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i) :
    commonFaceDim a b u x + commonFaceDim a b v x ≤
      d + (n - 2 * d) := by
  let U : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := commonDirection a b u x
  let V : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := commonDirection a b v x
  have hinter : Module.finrank ℝ (U ⊓ V) ≤ n - 2 * d := by
    simpa [U, V] using
      common_direction_intersection_finrank_le_excess a b u v x hu hv hx hsep
  have hsup : Module.finrank ℝ (U ⊔ V) ≤ d := by
    have h := Submodule.finrank_le (U ⊔ V)
    simpa using h
  change Module.finrank ℝ U + Module.finrank ℝ V ≤ d + (n - 2 * d)
  rw [← Submodule.finrank_sup_add_finrank_inf_eq U V]
  exact Nat.add_le_add hsup hinter

/-- General separated face splitter. Let
`H = d + (n-2d)`. To reach a point whose common face with the target has
dimension at most `H-R`, it is enough to control graph diameter only in
ambient dimensions at most `R-1`.

For balanced instances `H=d`, recovering a symmetric source/target split.
For positive excess the neutral rows account exactly for the extra `n-2d`
slack in the dimension budget. -/
theorem separated_common_face_split_core
    (d n R B : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i)
    (hR0 : 1 ≤ R) (hRd : R ≤ d)
    (hconnect : ∃ D : ℕ, ∃ wg : ℕ → EuclideanSpace ℝ (Fin d),
      wg 0 = u ∧ wg D = v ∧
      ∀ j < D, wg j = wg (j + 1) ∨
        Adj (Hpoly a b) (wg j) (wg (j + 1)))
    (hlow : ∀ (e : ℕ), e ≤ R - 1 →
      ∀ (a' : Fin n → EuclideanSpace ℝ (Fin e)) (b' : Fin n → ℝ),
        (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
        DiamLE (Hpoly a' b') B) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Hpoly a b) ∧
      commonFaceDim a b v z ≤ d + (n - 2 * d) - R ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (B + 1) = z ∧
        ∀ j < B + 1,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  let H := d + (n - 2 * d)
  let T : EuclideanSpace ℝ (Fin d) → Prop := fun y =>
    commonFaceDim a b v y ≤ H - R
  have h2d : 2 * d ≤ n :=
    separated_extremes_n_ge_two_d a b u v hu hv hsep
  have hRH : R ≤ H := by
    dsimp [H]
    omega
  have hself : commonFaceDim a b v v = 0 := by
    have hbot : commonDirection a b v v = (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin d))) := by
      ext q
      constructor
      · intro hq
        have hq0 : q = 0 := by
          apply vertex_tight_rows_span_checked d n a b v hv q
          intro i hiv
          by_cases hai : a i = 0
          · simp [hai]
          · have hiC : i ∈ commonSourceRows a b v v := by
              simp [commonSourceRows, hai, hiv]
            have hker : rowEvalMap a (commonSourceRows a b v v) q = 0 :=
              LinearMap.mem_ker.1 hq
            exact congrFun hker ⟨i, hiC⟩
        simpa [hq0]
      · intro hq
        simpa using hq
    rw [commonFaceDim, hbot]
    simp
  have hTv : T v := by
    dsimp [T]
    rw [hself]
    omega
  have hboundary : ∀ x z, Adj (Hpoly a b) x z → ¬ T x → T z →
      commonFaceDim a b u x ≤ R - 1 := by
    intro x z hxz hxT _hzT
    have hxext : x ∈ extremePoints ℝ (Hpoly a b) :=
      adj_left_extreme (Hpoly a b) hxz
    have hsum := commonFaceDim_add_le_dim_add_excess
      a b u v x hu hv hxext hsep
    have hvlarge : H - R < commonFaceDim a b v x := by
      change ¬ commonFaceDim a b v x ≤ H - R at hxT
      exact Nat.lt_of_not_ge hxT
    dsimp [H] at hvlarge
    omega
  simpa [H, T] using
    (HirschPrescribed.target_set_access_of_boundary_face_dim_core
      d n (R - 1) B a b hbd u v hu T hTv hboundary hconnect hlow)

#print axioms common_direction_intersection_finrank_le_neutral_card
#print axioms commonFaceDim_add_le_dim_add_excess
#print axioms separated_common_face_split_core

end HirschPolynomialAccess
