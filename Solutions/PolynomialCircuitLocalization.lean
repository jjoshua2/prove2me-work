import Mathlib
import Definitions.Def_Hirsch_circuit_model
import Solutions.PolynomialCommonFaceCoords

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCircuitLocalization

open HirschPolynomialAccess

variable {d n : ℕ}

noncomputable def sourceOnlyRows
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter (fun i =>
    a i ≠ 0 ∧ ⟪a i, u⟫ = b i ∧ ⟪a i, v⟫ ≠ b i)

noncomputable def targetOnlyRows
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter (fun i =>
    a i ≠ 0 ∧ ⟪a i, u⟫ ≠ b i ∧ ⟪a i, v⟫ = b i)

noncomputable def circuitNeutralRows
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, g⟫ = 0)

/-- The common-face direction space injects into the rows tight only at the
source vertex. Consequently its dimension is bounded by the number of such
rows. No simplicity or irredundancy hypothesis is needed. -/
theorem commonFaceDim_le_sourceOnlyRows_card
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b)) :
    commonFaceDim a b u v ≤ (sourceOnlyRows a b u v).card := by
  classical
  let C := commonSourceRows a b u v
  let S := sourceOnlyRows a b u v
  let W := commonDirection a b u v
  let T : W →ₗ[ℝ] (S → ℝ) := (rowEvalMap a S).domRestrict W
  have hTin : Function.Injective T := by
    intro y z hyz
    apply Subtype.ext
    let q : W := y - z
    have hTq : T q = 0 := by
      change T (y - z) = 0
      rw [map_sub, hyz, sub_self]
    have hqC : ∀ i, i ∈ C →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hi
      have hker : rowEvalMap a C (q : EuclideanSpace ℝ (Fin d)) = 0 := by
        apply LinearMap.mem_ker.1
        exact q.property
      exact congrFun hker ⟨i, hi⟩
    have hqS : ∀ i, i ∈ S →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hi
      change T q ⟨i, hi⟩ = 0
      exact congrFun hTq ⟨i, hi⟩
    have hqtight : ∀ i, ⟪a i, u⟫ = b i →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hiu
      by_cases hai : a i = 0
      · simp [hai]
      by_cases hiv : ⟪a i, v⟫ = b i
      · exact hqC i (by simp [C, commonSourceRows, hai, hiu, hiv])
      · exact hqS i (by simp [S, sourceOnlyRows, hai, hiu, hiv])
    have hq0 := HirschPolynomialAccess.vertex_tight_rows_span_checked
      d n a b u hu (q : EuclideanSpace ℝ (Fin d)) hqtight
    change (y : EuclideanSpace ℝ (Fin d)) -
      (z : EuclideanSpace ℝ (Fin d)) = 0 at hq0
    exact sub_eq_zero.mp hq0
  have hle := LinearMap.finrank_le_finrank_of_injective hTin
  simpa [commonFaceDim, W, S] using hle

/-- The same common-face direction space injects into the rows tight only at
the target vertex. -/
theorem commonFaceDim_le_targetOnlyRows_card
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    commonFaceDim a b u v ≤ (targetOnlyRows a b u v).card := by
  classical
  let C := commonSourceRows a b u v
  let S := targetOnlyRows a b u v
  let W := commonDirection a b u v
  let T : W →ₗ[ℝ] (S → ℝ) := (rowEvalMap a S).domRestrict W
  have hTin : Function.Injective T := by
    intro y z hyz
    apply Subtype.ext
    let q : W := y - z
    have hTq : T q = 0 := by
      change T (y - z) = 0
      rw [map_sub, hyz, sub_self]
    have hqC : ∀ i, i ∈ C →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hi
      have hker : rowEvalMap a C (q : EuclideanSpace ℝ (Fin d)) = 0 := by
        apply LinearMap.mem_ker.1
        exact q.property
      exact congrFun hker ⟨i, hi⟩
    have hqS : ∀ i, i ∈ S →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hi
      change T q ⟨i, hi⟩ = 0
      exact congrFun hTq ⟨i, hi⟩
    have hqtight : ∀ i, ⟪a i, v⟫ = b i →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hiv
      by_cases hai : a i = 0
      · simp [hai]
      by_cases hiu : ⟪a i, u⟫ = b i
      · exact hqC i (by simp [C, commonSourceRows, hai, hiu, hiv])
      · exact hqS i (by simp [S, targetOnlyRows, hai, hiu, hiv])
    have hq0 := HirschPolynomialAccess.vertex_tight_rows_span_checked
      d n a b v hv (q : EuclideanSpace ℝ (Fin d)) hqtight
    change (y : EuclideanSpace ℝ (Fin d)) -
      (z : EuclideanSpace ℝ (Fin d)) = 0 at hq0
    exact sub_eq_zero.mp hq0
  have hle := LinearMap.finrank_le_finrank_of_injective hTin
  simpa [commonFaceDim, W, S] using hle

/-- A row-circuit direction has at least `d-1` distinct nonzero neutral rows
as soon as one endpoint is a vertex. This is a cardinality consequence of
support minimality; no irredundancy or simplicity assumption is used. -/
theorem circuitNeutralRows_card_ge_dim_sub_one
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u g : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hg : IsRowCircuit a g) :
    d - 1 ≤ (circuitNeutralRows a g).card := by
  classical
  by_cases hd : d ≤ 1
  · omega
  have hd2 : 2 ≤ d := by omega
  let Z := circuitNeutralRows a g
  by_contra hcard
  have hZlt : Z.card < d - 1 := Nat.lt_of_not_ge hcard
  have hex : ∃ i : Fin n, ⟪a i, g⟫ ≠ 0 := by
    by_contra hn
    have hall : ∀ i : Fin n, ⟪a i, g⟫ = 0 := by
      intro i
      by_contra hi
      exact hn ⟨i, hi⟩
    have hg0 := HirschPolynomialAccess.vertex_tight_rows_span_checked
      d n a b u hu g (fun i _ => hall i)
    exact hg.1 hg0
  obtain ⟨i0, hi0g⟩ := hex
  have hi0a : a i0 ≠ 0 := by
    intro hi0
    rw [hi0, inner_zero_left] at hi0g
    exact hi0g rfl
  have hi0Z : i0 ∉ Z := by
    simp [Z, circuitNeutralRows, hi0a, hi0g]
  let S : Finset (Fin n) := insert i0 Z
  have hScard : S.card = Z.card + 1 := by
    simp [S, hi0Z]
  have hSlt : S.card < d := by
    rw [hScard]
    omega
  let T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (S → ℝ) := rowEvalMap a S
  have hnotinj : ¬ Function.Injective T := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    have hdom : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
      finrank_euclideanSpace_fin (𝕜 := ℝ)
    have hcod : Module.finrank ℝ (S → ℝ) = S.card := by
      simp [Fintype.card_coe]
    rw [hdom, hcod] at hle
    omega
  have hker : T.ker ≠ ⊥ := by
    intro hk
    apply hnotinj
    rw [← LinearMap.ker_eq_bot]
    exact hk
  obtain ⟨h, hhker, hh0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hTh : T h = 0 := LinearMap.mem_ker.1 hhker
  have hsub : circuitRowSupport a h ⊆ circuitRowSupport a g := by
    intro i hi
    change ⟪a i, h⟫ ≠ 0 at hi
    change ⟪a i, g⟫ ≠ 0
    intro hig
    have hai : a i ≠ 0 := by
      intro ha0
      rw [ha0, inner_zero_left] at hi
      exact hi rfl
    have hiZ : i ∈ Z := by
      simp [Z, circuitNeutralRows, hai, hig]
    have hiS : i ∈ S := by
      simp [S, hiZ]
    have hcoord := congrFun hTh ⟨i, hiS⟩
    change ⟪a i, h⟫ = 0 at hcoord
    exact hi hcoord
  have hrev := hg.2 h hh0 hsub
  have hi0supp : i0 ∈ circuitRowSupport a g := by
    exact hi0g
  have hi0hsupp := hrev hi0supp
  change ⟪a i0, h⟫ ≠ 0 at hi0hsupp
  have hi0S : i0 ∈ S := by simp [S]
  have hi0zero := congrFun hTh ⟨i0, hi0S⟩
  change ⟪a i0, h⟫ = 0 at hi0zero
  exact hi0hsupp hi0zero

/-- Sharp row-count localization for a vertex-to-vertex row-circuit
displacement. In subtraction-free form:

`2 * dim F(u,v) + d ≤ n + 1`.

Here `commonFaceDim` is the rank-correct dimension of the common-source face.
No simplicity, irredundancy, strict feasibility, or maximal-step hypothesis is
required beyond the two vertex assumptions and the row-circuit property. -/
theorem rowCircuit_commonFaceDim_localization
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u)) :
    2 * commonFaceDim a b u v + d ≤ n + 1 := by
  classical
  let S := sourceOnlyRows a b u v
  let T := targetOnlyRows a b u v
  let Z := circuitNeutralRows a (v - u)
  have hSdim : commonFaceDim a b u v ≤ S.card := by
    simpa [S] using commonFaceDim_le_sourceOnlyRows_card a b u v hu
  have hTdim : commonFaceDim a b u v ≤ T.card := by
    simpa [T] using commonFaceDim_le_targetOnlyRows_card a b u v hv
  have hZdim : d - 1 ≤ Z.card := by
    simpa [Z] using circuitNeutralRows_card_ge_dim_sub_one a b u (v - u) hu hcirc
  have hST : Disjoint S T := by
    refine Finset.disjoint_left.2 ?_
    intro i hiS hiT
    have hs := (Finset.mem_filter.1 hiS).2
    have ht := (Finset.mem_filter.1 hiT).2
    exact ht.2.1 hs.2.1
  have hSZ : Disjoint S Z := by
    refine Finset.disjoint_left.2 ?_
    intro i hiS hiZ
    have hs := (Finset.mem_filter.1 hiS).2
    have hz := (Finset.mem_filter.1 hiZ).2
    have hz0 : ⟪a i, v - u⟫ = 0 := hz.2
    rw [inner_sub_right] at hz0
    have hvEq : ⟪a i, v⟫ = b i := by linarith [hs.2.1]
    exact hs.2.2 hvEq
  have hTZ : Disjoint T Z := by
    refine Finset.disjoint_left.2 ?_
    intro i hiT hiZ
    have ht := (Finset.mem_filter.1 hiT).2
    have hz := (Finset.mem_filter.1 hiZ).2
    have hz0 : ⟪a i, v - u⟫ = 0 := hz.2
    rw [inner_sub_right] at hz0
    have huEq : ⟪a i, u⟫ = b i := by linarith [ht.2.2]
    exact ht.2.1 huEq
  have hSTZ : Disjoint (S ∪ T) Z := Finset.disjoint_union_left.2 ⟨hSZ, hTZ⟩
  have htotal : (S ∪ T ∪ Z).card ≤ n := by
    have hsub : S ∪ T ∪ Z ⊆ (Finset.univ : Finset (Fin n)) := by simp
    calc
      (S ∪ T ∪ Z).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card hsub
      _ = n := by simp
  rw [Finset.card_union_of_disjoint hSTZ,
      Finset.card_union_of_disjoint hST] at htotal
  omega

/-- Equivalent excess-style corollary of the subtraction-free localization
bound. -/
theorem rowCircuit_commonFaceDim_twice_le_excess_add_one
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u)) :
    2 * commonFaceDim a b u v ≤ n - d + 1 := by
  have hloc := rowCircuit_commonFaceDim_localization a b u v hu hv hcirc
  have hd : d ≤ n := by
    have hrows := HirschPolynomialAccess.nonzero_tight_rows_card_ge_dim a b u hu
    have hsub :
        (Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, u⟫ = b i)).card ≤ n := by
      calc
        _ ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card (by simp)
        _ = n := by simp
    exact hrows.trans hsub
  omega

#print axioms commonFaceDim_le_sourceOnlyRows_card
#print axioms commonFaceDim_le_targetOnlyRows_card
#print axioms circuitNeutralRows_card_ge_dim_sub_one
#print axioms rowCircuit_commonFaceDim_localization
#print axioms rowCircuit_commonFaceDim_twice_le_excess_add_one

end HirschCircuitLocalization
