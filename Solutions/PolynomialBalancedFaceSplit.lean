import Mathlib
import Solutions.PolynomialBalancedTargetRank

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option maxHeartbeats 5000000

noncomputable section

namespace HirschPolynomialAccess

/-- For any vertex `x` in an exactly balanced separated instance, the
common-direction spaces from the source and from the target are disjoint.
Every row tight at `x` belongs to exactly one endpoint class; a vector in both
common-direction spaces is therefore orthogonal to every row tight at `x`,
and vertex extremality forces it to vanish. -/
theorem balanced_commonDirection_disjoint
    (d : ℕ)
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d))
    (b : Fin (2 * d) → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i) :
    Disjoint (commonDirection a b u x) (commonDirection a b v x) := by
  rw [Submodule.disjoint_def]
  intro q hqu hqv
  apply vertex_tight_rows_span_checked d (2 * d) a b x hx q
  intro i hix
  have hpart := balanced_rows_partition d a b u v hu hv hsep i
  rcases hpart with ⟨hai, hsource | htarget⟩
  · have hiC : i ∈ commonSourceRows a b u x := by
      simp [commonSourceRows, hai, hsource.1, hix]
    have hker : rowEvalMap a (commonSourceRows a b u x) q = 0 :=
      LinearMap.mem_ker.1 hqu
    exact congrFun hker ⟨i, hiC⟩
  · have hiC : i ∈ commonSourceRows a b v x := by
      simp [commonSourceRows, hai, htarget.2, hix]
    have hker : rowEvalMap a (commonSourceRows a b v x) q = 0 :=
      LinearMap.mem_ker.1 hqv
    exact congrFun hker ⟨i, hiC⟩

/-- Two-sided dimension tradeoff at every intermediate vertex of a balanced
separated instance:

`dim F(u,x) + dim F(v,x) ≤ d`.

This is stronger than counting how many target rows have been acquired and is
independent of any graph-diameter theorem. -/
theorem balanced_commonFaceDim_add_le_dim
    (d : ℕ)
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d))
    (b : Fin (2 * d) → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i) :
    commonFaceDim a b u x + commonFaceDim a b v x ≤ d := by
  have hdisj := balanced_commonDirection_disjoint d a b u v x hu hv hx hsep
  have hle := Submodule.finrank_add_finrank_le_of_disjoint hdisj
  simpa [commonFaceDim] using hle

/-- The common-direction space of a vertex with itself is zero. -/
theorem commonDirection_self_eq_bot {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    commonDirection a b v v = ⊥ := by
  apply Submodule.eq_bot_iff.mpr
  intro q hq
  apply vertex_tight_rows_span_checked d n a b v hv q
  intro i hiv
  by_cases hai : a i = 0
  · simp [hai]
  · have hiC : i ∈ commonSourceRows a b v v := by
      simp [commonSourceRows, hai, hiv]
    have hker : rowEvalMap a (commonSourceRows a b v v) q = 0 :=
      LinearMap.mem_ker.1 hq
    exact congrFun hker ⟨i, hiC⟩

@[simp] theorem commonFaceDim_self {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    commonFaceDim a b v v = 0 := by
  rw [commonFaceDim, commonDirection_self_eq_bot a b v hv]
  simp

/-- A two-sided balanced face splitter. To reach a point whose common face
with the target has dimension at most `d-R`, it is enough to control graph
diameter only in dimensions at most `R-1`.

Choosing `R` near `d/2` makes the source-shortcut face and the resulting
target-common face simultaneously about half-dimensional. The statement is a
geometric reduction core; it does not assume a conjectural global diameter
bound itself. -/
theorem balanced_common_face_split_core
    (d R B : ℕ)
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d))
    (b : Fin (2 * d) → ℝ)
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
      ∀ (a' : Fin (2 * d) → EuclideanSpace ℝ (Fin e))
        (b' : Fin (2 * d) → ℝ),
        (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
        DiamLE (Hpoly a' b') B) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Hpoly a b) ∧
      commonFaceDim a b v z ≤ d - R ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (B + 1) = z ∧
        ∀ j < B + 1,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  let T : EuclideanSpace ℝ (Fin d) → Prop := fun y =>
    commonFaceDim a b v y ≤ d - R
  have hTv : T v := by
    dsimp [T]
    rw [commonFaceDim_self a b v hv]
    omega
  have hboundary : ∀ x z, Adj (Hpoly a b) x z → ¬ T x → T z →
      commonFaceDim a b u x ≤ R - 1 := by
    intro x z hxz hxT _hzT
    have hxext : x ∈ extremePoints ℝ (Hpoly a b) :=
      adj_left_extreme (Hpoly a b) hxz
    have hsum := balanced_commonFaceDim_add_le_dim
      d a b u v x hu hv hxext hsep
    have hvlarge : d - R < commonFaceDim a b v x := by
      exact Nat.lt_of_not_ge hxT
    omega
  exact HirschPrescribed.target_set_access_of_boundary_face_dim_core
    d (2 * d) (R - 1) B a b hbd u v hu T hTv hboundary hconnect hlow

#print axioms balanced_commonDirection_disjoint
#print axioms balanced_commonFaceDim_add_le_dim
#print axioms commonDirection_self_eq_bot
#print axioms balanced_common_face_split_core

end HirschPolynomialAccess
