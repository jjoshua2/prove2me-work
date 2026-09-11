import Solutions.PolynomialVertexSpan

/-!
# Direct small-excess descent

The two geometric library inputs are explicit propositions, not axioms or
imported theorem stubs. They match the live Prove2Me statements of
`Hirsch.dimension_three_bound` and `Hirsch.facet_reduction`.

A separate platform solution supplies those already-Proved inputs. This driver
also exposes the nonzero-row counting needed when tautologies are present.
-/

open Set Hirsch
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section
namespace HirschLowExcess

noncomputable def tightNonzeroRows {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, x⟫ = b i)

/-- A vertex has at least d distinct tight nonzero describing rows. -/
theorem dimension_le_tightNonzeroRows_card {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b)) :
    d ≤ (tightNonzeroRows a b x).card := by
  classical
  let S := tightNonzeroRows a b x
  let T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun y i => ⟪a i.1, y⟫
      map_add' := by
        intro y z
        funext i
        simp [inner_add_right]
      map_smul' := by
        intro r y
        funext i
        simp [inner_smul_right] }
  have hT : Function.Injective T := by
    intro y z hyz
    apply sub_eq_zero.mp
    apply HirschPolynomialAccess.vertex_tight_rows_span_checked d n a b x hx (y - z)
    intro i hi
    by_cases hai : a i = 0
    · simp [hai]
    · have hiS : i ∈ S := by simp [S, tightNonzeroRows, hai, hi]
      have hrow := congrFun hyz ⟨i, hiS⟩
      change ⟪a i, y⟫ = ⟪a i, z⟫ at hrow
      rw [inner_sub_right, hrow, sub_self]
  have hdim := LinearMap.finrank_le_finrank_of_injective hT
  simpa [S] using hdim

/-- The shared tight row can be chosen nonzero even with zero tautologies. -/
theorem vertices_share_nonzero_tight_row_of_n_lt_two_d {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b)) (hn : n < 2 * d) :
    ∃ i : Fin n, a i ≠ 0 ∧ ⟪a i, u⟫ = b i ∧ ⟪a i, v⟫ = b i := by
  classical
  let U := tightNonzeroRows a b u
  let V := tightNonzeroRows a b v
  have huCard : d ≤ U.card := dimension_le_tightNonzeroRows_card a b u hu
  have hvCard : d ≤ V.card := dimension_le_tightNonzeroRows_card a b v hv
  by_contra hnone
  have hdis : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro i hiU hiV
    have hU : a i ≠ 0 ∧ ⟪a i, u⟫ = b i := by
      simpa [U, tightNonzeroRows] using hiU
    have hV : a i ≠ 0 ∧ ⟪a i, v⟫ = b i := by
      simpa [V, tightNonzeroRows] using hiV
    exact hnone ⟨i, hU.1, hU.2, hV.2⟩
  have hsum := Finset.card_union_of_disjoint hdis
  have hbound : (U ∪ V).card ≤ n := by
    calc
      (U ∪ V).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  omega

/-- Exact type of the already-Proved low-dimensional Hirsch input. -/
def LowDimensionalHirsch : Prop :=
  ∀ (d n : ℕ), d ≤ 3 →
    ∀ (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      (Hpoly a b).Nonempty → Bornology.IsBounded (Hpoly a b) →
      DiamLE (Hpoly a b) (n - d)

/-- Exact type of the already-Proved equality-section/facet reduction input.
Only ambient edge routing is requested, matching the public theorem. -/
def FacetWalkReduction : Prop :=
  ∀ (d k : ℕ) (a : Fin (k + 1) → EuclideanSpace ℝ (Fin d))
    (b : Fin (k + 1) → ℝ) (i : Fin (k + 1)), a i ≠ 0 →
    Bornology.IsBounded (Hpoly a b) → ∀ B : ℕ,
    (∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin k → ℝ),
      Bornology.IsBounded (Hpoly a' b') → DiamLE (Hpoly a' b') B) →
    ∀ (u v : EuclideanSpace ℝ (Fin d)),
      u ∈ extremePoints ℝ {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i} →
      v ∈ extremePoints ℝ {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i} →
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = u ∧ w B = v ∧
        ∀ j < B, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1))

/-- Descent preserves n-d and adds no access cost. Empty sets are included. -/
theorem hpoly_diameter_le_excess_from_proved_inputs
    (hbase : LowDimensionalHirsch) (hfacet : FacetWalkReduction) :
    ∀ (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      n ≤ d + 3 → Bornology.IsBounded (Hpoly a b) →
      DiamLE (Hpoly a b) (n - d) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro n a b hrows hbd
    by_cases hd : d ≤ 3
    · by_cases hne : (Hpoly a b).Nonempty
      · exact hbase d n hd a b hne hbd
      · intro u hu
        exact False.elim (hne ⟨u, hu.1⟩)
    · intro u hu v hv
      have hsub : n < 2 * d := by omega
      obtain ⟨i, hai, hui, hvi⟩ :=
        vertices_share_nonzero_tight_row_of_n_lt_two_d a b u v hu hv hsub
      cases n with
      | zero => exact Fin.elim0 i
      | succ k =>
        have hlow : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1)))
            (b' : Fin k → ℝ), Bornology.IsBounded (Hpoly a' b') →
            DiamLE (Hpoly a' b') (k + 1 - d) := by
          intro a' b' hbd'
          have hsmall : d - 1 < d := by omega
          have hrows' : k ≤ (d - 1) + 3 := by omega
          have hbound := ih (d - 1) hsmall k a' b' hrows' hbd'
          have heq : k - (d - 1) = k + 1 - d := by omega
          rw [heq] at hbound
          exact hbound
        have huF : u ∈ extremePoints ℝ
            {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i} := by
          refine ⟨⟨hu.1, hui⟩, ?_⟩
          intro x hx y hy hseg
          exact hu.2 hx.1 hy.1 hseg
        have hvF : v ∈ extremePoints ℝ
            {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i} := by
          refine ⟨⟨hv.1, hvi⟩, ?_⟩
          intro x hx y hy hseg
          exact hv.2 hx.1 hy.1 hseg
        exact hfacet d k a b i hai hbd (k + 1 - d) hlow u v huF hvF

#print axioms dimension_le_tightNonzeroRows_card
#print axioms vertices_share_nonzero_tight_row_of_n_lt_two_d
#print axioms hpoly_diameter_le_excess_from_proved_inputs

end HirschLowExcess
end
