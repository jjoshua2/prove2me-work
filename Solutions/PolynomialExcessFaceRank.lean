import Mathlib
import Definitions.Def_Hirsch_model
import Solutions.PolynomialSeparatedRows

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option maxHeartbeats 3000000

noncomputable section

namespace HirschPolynomialAccess

variable {d n : ℕ}

noncomputable def commonSourceRows
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter (fun i =>
    a i ≠ 0 ∧ ⟪a i, u⟫ = b i ∧ ⟪a i, x⟫ = b i)

noncomputable def neutralRows
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter (fun i =>
    a i ≠ 0 ∧ ⟪a i, u⟫ ≠ b i ∧ ⟪a i, v⟫ ≠ b i)

noncomputable def rowEvalMap
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (S : Finset (Fin n)) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (S → ℝ) :=
  { toFun := fun y i => ⟪a i.1, y⟫
    map_add' := by
      intro y z
      funext i
      simp [inner_add_right]
    map_smul' := by
      intro c y
      funext i
      simp [inner_smul_right] }

/-- Directions annihilating every nonzero row active at both `u` and `x`. -/
noncomputable def commonDirection
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  (rowEvalMap a (commonSourceRows a b u x)).ker

/-- Neutral-row evaluation is injective on the common-source directions of
any target-avoiding vertex. Separation and extremality of `u,v` are not needed. -/
lemma neutral_eval_injective
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (havoid : ∀ i, a i ≠ 0 →
      ⟪a i, v⟫ = b i → ⟪a i, x⟫ ≠ b i) :
    Function.Injective
      ((rowEvalMap a (neutralRows a b u v)).domRestrict
        (commonDirection a b u x)) := by
  classical
  let C := commonSourceRows a b u x
  let N := neutralRows a b u v
  let W := commonDirection a b u x
  let T : W →ₗ[ℝ] (N → ℝ) := (rowEvalMap a N).domRestrict W
  change Function.Injective T
  intro y z hyz
  apply Subtype.ext
  let q : W := y - z
  have hTq : T q = 0 := by
    rw [map_sub, hyz, sub_self]
  have hqCommon : ∀ i, i ∈ C → ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
    intro i hiC
    have hker : (rowEvalMap a C) (q : EuclideanSpace ℝ (Fin d)) = 0 :=
      LinearMap.mem_ker.1 q.2
    change (rowEvalMap a C) (q : EuclideanSpace ℝ (Fin d)) ⟨i, hiC⟩ = 0
    exact congrFun hker ⟨i, hiC⟩
  have hqNeutral : ∀ i, i ∈ N → ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
    intro i hiN
    change T q ⟨i, hiN⟩ = 0
    exact congrFun hTq ⟨i, hiN⟩
  have hqTight : ∀ i, ⟪a i, x⟫ = b i →
      ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
    intro i hix
    by_cases hai : a i = 0
    · simp [hai]
    by_cases hiu : ⟪a i, u⟫ = b i
    · have hiC : i ∈ C := by
        simp [C, commonSourceRows, hai, hiu, hix]
      exact hqCommon i hiC
    · have hiv : ⟪a i, v⟫ ≠ b i := by
        intro hivEq
        exact (havoid i hai hivEq) hix
      have hiN : i ∈ N := by
        simp [N, neutralRows, hai, hiu, hiv]
      exact hqNeutral i hiN
  have hq0 := vertex_tight_rows_span_checked d n a b x hx
    (q : EuclideanSpace ℝ (Fin d)) hqTight
  change (y : EuclideanSpace ℝ (Fin d)) - (z : EuclideanSpace ℝ (Fin d)) = 0 at hq0
  exact sub_eq_zero.mp hq0

/-- Sharper than counting neutral rows: linearly dependent rows cost only
the rank of their joint evaluation map. -/
lemma common_direction_finrank_le_neutral_rank
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (havoid : ∀ i, a i ≠ 0 →
      ⟪a i, v⟫ = b i → ⟪a i, x⟫ ≠ b i) :
    Module.finrank ℝ (commonDirection a b u x) ≤
      Module.finrank ℝ (rowEvalMap a (neutralRows a b u v)).range := by
  let W := commonDirection a b u x
  let R := rowEvalMap a (neutralRows a b u v)
  let T : W →ₗ[ℝ] R.range := R.rangeRestrict.comp W.subtype
  have hTin : Function.Injective T := by
    intro y z h
    apply neutral_eval_injective a b u v x hx havoid
    exact congrArg Subtype.val h
  exact LinearMap.finrank_le_finrank_of_injective hTin

/-- The original neutral-count estimate, now deduced from an explicit injective map. -/
lemma common_direction_finrank_le_neutral_card
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (_hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i)
    (havoid : ∀ i, a i ≠ 0 →
      ⟪a i, v⟫ = b i → ⟪a i, x⟫ ≠ b i) :
    Module.finrank ℝ (commonDirection a b u x) ≤
      (neutralRows a b u v).card := by
  have hle := LinearMap.finrank_le_finrank_of_injective
    (neutral_eval_injective a b u v x hx havoid)
  simpa using hle

/-- There are at most `n - 2*d` neutral rows for separated extreme endpoints. -/
lemma neutral_card_le_excess
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i) :
    (neutralRows a b u v).card ≤ n - 2 * d := by
  classical
  let SU : Finset (Fin n) :=
    Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, u⟫ = b i)
  let SV : Finset (Fin n) :=
    Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, v⟫ = b i)
  let N := neutralRows a b u v
  have hU : d ≤ SU.card := by
    simpa [SU] using nonzero_tight_rows_card_ge_dim a b u hu
  have hV : d ≤ SV.card := by
    simpa [SV] using nonzero_tight_rows_card_ge_dim a b v hv
  have hUV : Disjoint SU SV := by
    refine Finset.disjoint_left.2 ?_
    intro i hiU hiV
    have hu' := (Finset.mem_filter.1 hiU).2
    have hv' := (Finset.mem_filter.1 hiV).2
    rcases hsep i hu'.1 with hnu | hnv
    · exact hnu hu'.2
    · exact hnv hv'.2
  have hUN : Disjoint SU N := by
    refine Finset.disjoint_left.2 ?_
    intro i hiU hiN
    exact (Finset.mem_filter.1 hiN).2.2.1 (Finset.mem_filter.1 hiU).2.2
  have hVN : Disjoint SV N := by
    refine Finset.disjoint_left.2 ?_
    intro i hiV hiN
    exact (Finset.mem_filter.1 hiN).2.2.2 (Finset.mem_filter.1 hiV).2.2
  have hdisj : Disjoint (SU ∪ SV) N := Finset.disjoint_union_left.2 ⟨hUN, hVN⟩
  have hcardUnion : (SU ∪ SV).card = SU.card + SV.card :=
    Finset.card_union_of_disjoint hUV
  have htotal : (SU ∪ SV ∪ N).card ≤ n := by
    have hsub : SU ∪ SV ∪ N ⊆ (Finset.univ : Finset (Fin n)) := by simp
    calc
      (SU ∪ SV ∪ N).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card hsub
      _ = n := by simp
  rw [Finset.card_union_of_disjoint hdisj, hcardUnion] at htotal
  have h2d : 2 * d ≤ n := separated_extremes_n_ge_two_d a b u v hu hv hsep
  change N.card ≤ n - 2 * d
  omega

lemma common_direction_finrank_le_excess
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i)
    (havoid : ∀ i, a i ≠ 0 →
      ⟪a i, v⟫ = b i → ⟪a i, x⟫ ≠ b i) :
    Module.finrank ℝ (commonDirection a b u x) ≤ n - 2 * d :=
  (common_direction_finrank_le_neutral_card a b u v x hx hsep havoid).trans
    (neutral_card_le_excess a b u v hu hv hsep)

#print axioms common_direction_finrank_le_neutral_rank
#print axioms common_direction_finrank_le_excess

end HirschPolynomialAccess
