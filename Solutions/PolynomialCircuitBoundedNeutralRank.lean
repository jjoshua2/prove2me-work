import Mathlib
import Solutions.CircuitSlackBounded
import Solutions.PolynomialCircuitFaceNeutralRank

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- A bounded nonempty H-polyhedron has at least ambient-dimension many rows.
Unlike `rows_ge_dimension_of_vertex`, no extreme-point hypothesis is needed. -/
theorem rows_ge_dimension_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ Hpoly a b) :
    d ≤ n := by
  have hinj := HirschCircuit.rowMap_injective_of_bounded a b hbd u hu
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hdom : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
    finrank_euclideanSpace_fin (𝕜 := ℝ)
  have hcod : Module.finrank ℝ (Fin n → ℝ) = n := by simp
  rw [hdom, hcod] at hle
  exact hle

/-- Boundedness, rather than vertexhood of the source checkpoint, is enough to
show that the rows neutral on a row-circuit direction have common kernel exactly
the circuit line. -/
theorem rowCircuit_neutral_kernel_eq_span_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ Hpoly a b)
    (g : EuclideanSpace ℝ (Fin d))
    (hg : IsRowCircuit a g) :
    (rowEvalMap a (circuitNeutralRows a g)).ker =
      Submodule.span ℝ ({g} : Set (EuclideanSpace ℝ (Fin d))) := by
  classical
  let Z := circuitNeutralRows a g
  have hinj := HirschCircuit.rowMap_injective_of_bounded a b hbd u hu
  have hex : ∃ i : Fin n, ⟪a i, g⟫ ≠ 0 := by
    by_contra hn
    have hall : ∀ i : Fin n, ⟪a i, g⟫ = 0 := by
      intro i
      by_contra hi
      exact hn ⟨i, hi⟩
    have hmap : HirschCircuit.rowMap a g = HirschCircuit.rowMap a 0 := by
      funext i
      simp [HirschCircuit.rowMap, hall i]
    exact hg.1 (hinj hmap)
  obtain ⟨i0, hi0g⟩ := hex
  apply le_antisymm
  · intro h hhker
    by_cases hh0 : h = 0
    · subst h
      exact Submodule.zero_mem _
    have hEval : rowEvalMap a Z h = 0 := by
      apply LinearMap.mem_ker.1
      simpa [Z] using hhker
    have hsub : circuitRowSupport a h ⊆ circuitRowSupport a g := by
      intro i hi
      change ⟪a i, h⟫ ≠ 0 at hi
      change ⟪a i, g⟫ ≠ 0
      intro hig
      have hai : a i ≠ 0 := by
        intro hai
        rw [hai, inner_zero_left] at hi
        exact hi rfl
      have hiZ : i ∈ Z := by
        simp [Z, circuitNeutralRows, hai, hig]
      have hzero := congrFun hEval ⟨i, hiZ⟩
      change ⟪a i, h⟫ = 0 at hzero
      exact hi hzero
    let c : ℝ := ⟪a i0, h⟫ / ⟪a i0, g⟫
    let k : EuclideanSpace ℝ (Fin d) := h - c • g
    have hkSub : circuitRowSupport a k ⊆ circuitRowSupport a g := by
      intro i hi
      change ⟪a i, k⟫ ≠ 0 at hi
      change ⟪a i, g⟫ ≠ 0
      intro hig
      have hhig : ⟪a i, h⟫ = 0 := by
        by_contra hhne
        have hiH : i ∈ circuitRowSupport a h := hhne
        have hiG := hsub hiH
        change ⟪a i, g⟫ ≠ 0 at hiG
        exact hiG hig
      have hkig : ⟪a i, k⟫ = 0 := by
        dsimp [k]
        rw [inner_sub_right, inner_smul_right, hhig, hig]
        ring
      exact hi hkig
    by_cases hk0 : k = 0
    · have heq : h = c • g := sub_eq_zero.mp hk0
      rw [heq]
      exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton g))
    · have hrev := hg.2 k hk0 hkSub
      have hi0G : i0 ∈ circuitRowSupport a g := hi0g
      have hi0K := hrev hi0G
      change ⟪a i0, k⟫ ≠ 0 at hi0K
      have hi0zero : ⟪a i0, k⟫ = 0 := by
        dsimp [k, c]
        rw [inner_sub_right, inner_smul_right, div_mul_cancel₀ _ hi0g]
        exact sub_self _
      exact (hi0K hi0zero).elim
  · apply Submodule.span_le.2
    intro h hh
    have heq : h = g := by simpa using hh
    subst h
    apply LinearMap.mem_ker.2
    funext i
    change ⟪a i.1, g⟫ = 0
    exact (Finset.mem_filter.1 i.2).2.2

/-- Rank-nullity form of the bounded nonvertex neutral-kernel theorem. -/
theorem rowCircuit_neutral_rank_eq_dim_sub_one_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ Hpoly a b)
    (g : EuclideanSpace ℝ (Fin d))
    (hg : IsRowCircuit a g) :
    Module.finrank ℝ (rowEvalMap a (circuitNeutralRows a g)).range = d - 1 := by
  let T := rowEvalMap a (circuitNeutralRows a g)
  have hker : T.ker = Submodule.span ℝ ({g} : Set (EuclideanSpace ℝ (Fin d))) := by
    simpa [T] using rowCircuit_neutral_kernel_eq_span_of_bounded a b hbd u hu g hg
  have hkerRank : Module.finrank ℝ T.ker = 1 := by
    rw [hker]
    exact finrank_span_singleton hg.1
  have hrank := T.finrank_range_add_finrank_ker
  have hdom : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
    finrank_euclideanSpace_fin (𝕜 := ℝ)
  rw [hkerRank, hdom] at hrank
  have hrank' := congrArg (fun m : ℕ => m - 1) hrank
  simpa using hrank'

/-- On the common carrier of a row-circuit displacement, ambient neutral rows
still have rank exactly `h-1` when the source checkpoint is merely feasible,
provided the parent is bounded. -/
theorem rowCircuit_neutral_rank_on_commonDirection_eq_commonFaceDim_sub_one_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b)
    (hcirc : IsRowCircuit a (v - u)) :
    Module.finrank ℝ
        (((rowEvalMap a (circuitNeutralRows a (v - u))).domRestrict
          (commonDirection a b u v)).range) =
      commonFaceDim a b u v - 1 := by
  have hgW : v - u ∈ commonDirection a b u v := by
    apply LinearMap.mem_ker.2
    funext i
    have hi := (Finset.mem_filter.1 i.2).2
    change ⟪a i.1, v - u⟫ = 0
    rw [inner_sub_right, hi.2.2, hi.2.1, sub_self]
  let T := (rowEvalMap a (circuitNeutralRows a (v - u))).domRestrict
    (commonDirection a b u v)
  let gw : commonDirection a b u v := ⟨v - u, hgW⟩
  have hker : T.ker = Submodule.span ℝ ({gw} : Set (commonDirection a b u v)) := by
    apply le_antisymm
    · intro x hx
      have hxamb : (x : EuclideanSpace ℝ (Fin d)) ∈
          (rowEvalMap a (circuitNeutralRows a (v - u))).ker := by
        apply LinearMap.mem_ker.2
        have hx0 := LinearMap.mem_ker.1 hx
        simpa [T] using hx0
      have hamb := rowCircuit_neutral_kernel_eq_span_of_bounded
        a b hbd u hu (v - u) hcirc
      rw [hamb] at hxamb
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxamb
      apply Submodule.mem_span_singleton.mpr
      refine ⟨c, ?_⟩
      apply Subtype.ext
      simpa [gw] using hc
    · apply Submodule.span_le.2
      intro x hx
      have hxgw : x = gw := by simpa [gw] using hx
      subst x
      apply LinearMap.mem_ker.2
      funext i
      change ⟪a i.1, v - u⟫ = 0
      exact (Finset.mem_filter.1 i.2).2.2
  have hgw0 : gw ≠ 0 := by
    intro h
    apply hcirc.1
    have hv := congrArg Subtype.val h
    simpa [gw] using hv
  have hkerRank : Module.finrank ℝ T.ker = 1 := by
    rw [hker]
    exact finrank_span_singleton hgw0
  have hrank := T.finrank_range_add_finrank_ker
  rw [hkerRank] at hrank
  have hrank' := congrArg (fun m : ℕ => m - 1) hrank
  simpa [T, commonFaceDim] using hrank'

#print axioms rows_ge_dimension_of_bounded
#print axioms rowCircuit_neutral_kernel_eq_span_of_bounded
#print axioms rowCircuit_neutral_rank_eq_dim_sub_one_of_bounded
#print axioms rowCircuit_neutral_rank_on_commonDirection_eq_commonFaceDim_sub_one_of_bounded

end HirschCircuitLocalization
