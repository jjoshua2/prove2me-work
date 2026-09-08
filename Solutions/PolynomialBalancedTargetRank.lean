import Mathlib
import Solutions.PolynomialPrescribedFaceCore
import Solutions.PolynomialSeparatedRows

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option maxHeartbeats 5000000

noncomputable section

namespace HirschPolynomialAccess

/-- Rows simultaneously tight at the fixed target `v` and a current point `x`.
In the balanced separated regime all rows are nonzero source or target rows,
but retaining the nonzero test makes the definition robust on its own. -/
noncomputable def targetActiveRows {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v x : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter (fun i =>
    a i ≠ 0 ∧ ⟪a i, v⟫ = b i ∧ ⟪a i, x⟫ = b i)

/-- At exact balance, two separated extreme points exhaust all rows: every
row is nonzero and is tight at exactly one of the two endpoints. -/
theorem balanced_rows_partition
    (d : ℕ)
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d))
    (b : Fin (2 * d) → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i) :
    ∀ i, a i ≠ 0 ∧
      ((⟪a i, u⟫ = b i ∧ ⟪a i, v⟫ ≠ b i) ∨
       (⟪a i, u⟫ ≠ b i ∧ ⟪a i, v⟫ = b i)) := by
  classical
  let SU : Finset (Fin (2 * d)) :=
    Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, u⟫ = b i)
  let SV : Finset (Fin (2 * d)) :=
    Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, v⟫ = b i)
  have hU : d ≤ SU.card := by
    simpa [SU] using nonzero_tight_rows_card_ge_dim a b u hu
  have hV : d ≤ SV.card := by
    simpa [SV] using nonzero_tight_rows_card_ge_dim a b v hv
  have hdisj : Disjoint SU SV := by
    refine Finset.disjoint_left.2 ?_
    intro i hiU hiV
    have hu' := (Finset.mem_filter.1 hiU).2
    have hv' := (Finset.mem_filter.1 hiV).2
    rcases hsep i hu'.1 with hnu | hnv
    · exact hnu hu'.2
    · exact hnv hv'.2
  have hUcard : SU.card = d := by
    have htotal : SU.card + SV.card ≤ 2 * d := by
      rw [← Finset.card_union_of_disjoint hdisj]
      have hsub : SU ∪ SV ⊆ (Finset.univ : Finset (Fin (2 * d))) := by simp
      simpa using Finset.card_le_card hsub
    omega
  have hVcard : SV.card = d := by
    have htotal : SU.card + SV.card ≤ 2 * d := by
      rw [← Finset.card_union_of_disjoint hdisj]
      have hsub : SU ∪ SV ⊆ (Finset.univ : Finset (Fin (2 * d))) := by simp
      simpa using Finset.card_le_card hsub
    omega
  have hcover : SU ∪ SV = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint hdisj, hUcard, hVcard]
    simpa [two_mul]
  intro i
  have hi : i ∈ SU ∪ SV := by rw [hcover]; simp
  rcases Finset.mem_union.1 hi with hiU | hiV
  · have hu' := (Finset.mem_filter.1 hiU).2
    have hnv : ⟪a i, v⟫ ≠ b i := by
      rcases hsep i hu'.1 with hnu | hnv
      · exact False.elim (hnu hu'.2)
      · exact hnv
    exact ⟨hu'.1, Or.inl ⟨hu'.2, hnv⟩⟩
  · have hv' := (Finset.mem_filter.1 hiV).2
    have hnu : ⟪a i, u⟫ ≠ b i := by
      rcases hsep i hv'.1 with hnu | hnv
      · exact hnu
      · exact False.elim (hnv hv'.2)
    exact ⟨hv'.1, Or.inr ⟨hnu, hv'.2⟩⟩

/-- In a balanced separated instance, evaluations on target rows already tight
at `x` separate the common-source directions of `u` and `x`.

This is the rank form of the counting observation behind the one-edge theorem:
any row tight at `x` that is not a common source row must be a target row. -/
theorem balanced_target_eval_injective
    (d : ℕ)
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d))
    (b : Fin (2 * d) → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i) :
    Function.Injective
      ((rowEvalMap a (targetActiveRows a b v x)).domRestrict
        (commonDirection a b u x)) := by
  classical
  let C := commonSourceRows a b u x
  let T := targetActiveRows a b v x
  let W := commonDirection a b u x
  let E : W →ₗ[ℝ] (T → ℝ) := (rowEvalMap a T).domRestrict W
  change Function.Injective E
  intro y z hyz
  apply Subtype.ext
  let q : W := y - z
  have hEq : E q = 0 := by
    rw [map_sub, hyz, sub_self]
  have hqCommon : ∀ i, i ∈ C →
      ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
    intro i hiC
    have hker : rowEvalMap a C (q : EuclideanSpace ℝ (Fin d)) = 0 :=
      LinearMap.mem_ker.1 q.property
    exact congrFun hker ⟨i, hiC⟩
  have hqTarget : ∀ i, i ∈ T →
      ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
    intro i hiT
    change E q ⟨i, hiT⟩ = 0
    exact congrFun hEq ⟨i, hiT⟩
  have hqTight : ∀ i, ⟪a i, x⟫ = b i →
      ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
    intro i hix
    have hpart := balanced_rows_partition d a b u v hu hv hsep i
    rcases hpart with ⟨hai, hsource | htarget⟩
    · have hiC : i ∈ C := by
        simp [C, commonSourceRows, hai, hsource.1, hix]
      exact hqCommon i hiC
    · have hiT : i ∈ T := by
        simp [T, targetActiveRows, hai, htarget.2, hix]
      exact hqTarget i hiT
  have hq0 := vertex_tight_rows_span_checked d (2 * d) a b x hx
    (q : EuclideanSpace ℝ (Fin d)) hqTight
  change (y : EuclideanSpace ℝ (Fin d)) -
    (z : EuclideanSpace ℝ (Fin d)) = 0 at hq0
  exact sub_eq_zero.mp hq0

/-- The common-source face dimension is bounded by the number of target rows
already reached at `x`.  The `R=1` case says that a vertex avoiding every
target row has zero-dimensional common-source face with `u`. -/
theorem balanced_commonFaceDim_le_target_card
    (d : ℕ)
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d))
    (b : Fin (2 * d) → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i) :
    commonFaceDim a b u x ≤ (targetActiveRows a b v x).card := by
  have hle := LinearMap.finrank_le_finrank_of_injective
    (balanced_target_eval_injective d a b u v x hu hv hx hsep)
  simpa [commonFaceDim] using hle

/-- Hierarchical balanced target access.

For `1 ≤ R ≤ d`, suppose every H-polytope with the same `2d` rows and
ambient dimension at most `R-1` has diameter at most `B`. Then a separated
balanced pair can reach, in `B+1` edge steps, a vertex on at least `R` of the
target's supporting rows.  The connectivity witness is deliberately
non-quantitative; only the low-dimensional diameter enters the budget. -/
theorem balanced_target_rank_access_core
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
      R ≤ (targetActiveRows a b v z).card ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (B + 1) = z ∧
        ∀ j < B + 1,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  classical
  let T : EuclideanSpace ℝ (Fin d) → Prop := fun y =>
    R ≤ (targetActiveRows a b v y).card
  have hTv : T v := by
    have hdcard : d ≤ (targetActiveRows a b v v).card := by
      simpa [targetActiveRows] using nonzero_tight_rows_card_ge_dim a b v hv
    exact hRd.trans hdcard
  have hboundary : ∀ x z, Adj (Hpoly a b) x z → ¬ T x → T z →
      commonFaceDim a b u x ≤ R - 1 := by
    intro x z hxz hxT _hzT
    have hxext : x ∈ extremePoints ℝ (Hpoly a b) :=
      adj_left_extreme (Hpoly a b) hxz
    have hdim := balanced_commonFaceDim_le_target_card
      d a b u v x hu hv hxext hsep
    have hcard : (targetActiveRows a b v x).card < R := by
      exact Nat.lt_of_not_ge hxT
    omega
  exact HirschPrescribed.target_set_access_of_boundary_face_dim_core
    d (2 * d) (R - 1) B a b hbd u v hu T hTv hboundary hconnect hlow

#print axioms balanced_rows_partition
#print axioms balanced_target_eval_injective
#print axioms balanced_commonFaceDim_le_target_card
#print axioms balanced_target_rank_access_core

end HirschPolynomialAccess
