import Mathlib
import Solutions.PolynomialNonvertexBlockerDeletion
import Solutions.CircuitPhaseBlockerPersistence
import Solutions.PolynomialHalfspaceVertex

open scoped RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschDeletion

/-- The unique-nonneutral exception is real: its nonzero direction belongs to
the kernel after deleting that row. -/
theorem rowMap_rowsWithout_not_injective_of_unique_nonneutral
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d)) (hg : g ≠ 0) (j : Fin n)
    (hneutral : ∀ i : Fin n, i ≠ j → ⟪a i, g⟫ = 0) :
    ¬ Function.Injective (HirschCircuit.rowMap (rowsWithout a j)) := by
  intro hinj
  apply hg
  apply hinj
  funext k
  change ⟪a (rowsWithoutEquiv j k).1, g⟫ =
    ⟪a (rowsWithoutEquiv j k).1, (0 : EuclideanSpace ℝ (Fin d))⟫
  rw [inner_zero_right]
  exact hneutral _ (rowsWithoutEquiv j k).2

/-- Exact deletion criterion for a nonneutral row of an injective circuit:
the deletion is pointed precisely when some other row is nonneutral. -/
theorem rowCircuit_pointed_deletion_iff_other_nonneutral
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (g : EuclideanSpace ℝ (Fin d)) (hg : IsRowCircuit a g)
    (j : Fin n) (hj : ⟪a j, g⟫ ≠ 0) :
    Function.Injective (HirschCircuit.rowMap (rowsWithout a j)) ↔
      ∃ i : Fin n, i ≠ j ∧ ⟪a i, g⟫ ≠ 0 := by
  constructor
  · intro hdel
    by_contra hnone
    have hneutral : ∀ i : Fin n, i ≠ j → ⟪a i, g⟫ = 0 := by
      intro i hij
      by_contra hi
      exact hnone ⟨i, hij, hi⟩
    exact rowMap_rowsWithout_not_injective_of_unique_nonneutral a g hg.1 j hneutral hdel
  · rintro ⟨i, hij, hi⟩
    exact rowMap_rowsWithout_injective_of_two_nonneutral_rowCircuit
      a hinj g hg i j hi hj hij

/-- A vertex survives removal of an inequality strictly slack there. The outer
need not be bounded or even separately known to be pointed. -/
theorem vertex_survives_rowsWithout_of_slack
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (j : Fin n) (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b)) (hvstrict : ⟪a j, v⟫ < b j) :
    v ∈ extremePoints ℝ (Hpoly (rowsWithout a j) (rhsWithout b j)) := by
  let ao := rowsWithout a j
  let bo := rhsWithout b j
  have hinter : Hpoly ao bo ∩ {z | ⟪a j, z⟫ ≤ b j} = Hpoly a b := by
    rw [show Hpoly ao bo = HirschCapVertices.deletionOuterSet a b j from
      hpoly_rowsWithout_eq_deletionOuterSet a b j]
    ext z
    constructor
    · rintro ⟨hrest, hj⟩ i
      by_cases hij : i = j
      · subst i
        exact hj
      · exact hrest i hij
    · intro hz
      exact ⟨fun i _ => hz i, hz j⟩
  have hconv : Convex ℝ (Hpoly ao bo) := by
    intro p hp q hq α β hα hβ hsum
    change ∀ i, ⟪ao i, α • p + β • q⟫ ≤ bo i
    intro i
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    calc
      α * ⟪ao i, p⟫ + β * ⟪ao i, q⟫ ≤ α * bo i + β * bo i :=
        add_le_add (mul_le_mul_of_nonneg_left (hp i) hα)
          (mul_le_mul_of_nonneg_left (hq i) hβ)
      _ = bo i := by rw [← add_mul, hsum, one_mul]
  have hvcut : v ∈ extremePoints ℝ (Hpoly ao bo ∩ {z | ⟪a j, z⟫ ≤ b j}) := by
    rw [hinter]
    exact hv
  exact HirschCut.strict_cut_extreme_to_parent (Hpoly ao bo) hconv (a j) (b j) hvcut hvstrict

/-- Stronger target-based criterion: deleting any row slack at a vertex
preserves pointedness. No circuit, source, or ambient injectivity premise is
needed: the surviving target vertex supplies the spanning tight rows. -/
theorem rowMap_rowsWithout_injective_of_slack_vertex
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (j : Fin n) (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b)) (hvstrict : ⟪a j, v⟫ < b j) :
    Function.Injective (HirschCircuit.rowMap (rowsWithout a j)) := by
  have hvdel := vertex_survives_rowsWithout_of_slack a b j v hv hvstrict
  intro p q hpq
  apply sub_eq_zero.mp
  apply HirschPolynomialAccess.vertex_tight_rows_span_checked d
    (Fintype.card {i : Fin n // i ≠ j}) (rowsWithout a j) (rhsWithout b j)
    v hvdel (p - q)
  intro i _
  have hi := congrFun hpq i
  change ⟪rowsWithout a j i, p⟫ = ⟪rowsWithout a j i, q⟫ at hi
  rw [inner_sub_right, hi, sub_self]

/-- Deletion really reduces the finite row count, including small dimensions. -/
theorem rowsWithout_card_lt
    {n : ℕ} (j : Fin n) : Fintype.card {i : Fin n // i ≠ j} < n := by
  classical
  have h := Fintype.card_lt_of_injective_not_surjective
    (fun i : {i : Fin n // i ≠ j} => i.1)
    (fun x y hxy => Subtype.ext hxy)
    (by
      intro hsurj
      obtain ⟨i, hi⟩ := hsurj j
      exact i.2 hi)
  simpa only [Fintype.card_fin] using h

/-- Every same-phase maximal circuit step admits a pointed blocker deletion
that preserves the fixed target as an actual vertex. The current checkpoint
need only be feasible. No compactness or source-vertex premise is used. -/
theorem rowCircuitStep_same_phase_has_target_preserving_pointed_deletion
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y v : EuclideanSpace ℝ (Fin d))
    (hstep : RowCircuitStep a b x y)
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (M : ℝ) (hM : 0 ≤ M) (r : Fin n → ℝ)
    (heqx : HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v) r =
      HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v) (HirschCircuit.slack a b x))
    (heqy : HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v) r =
      HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v) (HirschCircuit.slack a b y)) :
    ∃ j : Fin n,
      a j ≠ 0 ∧ ⟪a j, y⟫ = b j ∧ 0 < ⟪a j, y - x⟫ ∧
      ⟪a j, v⟫ < b j ∧ r j ≤ M * HirschCircuit.slack a b v j ∧
      Function.Injective (HirschCircuit.rowMap (rowsWithout a j)) ∧
      v ∈ extremePoints ℝ (Hpoly (rowsWithout a j) (rhsWithout b j)) := by
  obtain ⟨j, hja, hjy, hjpos⟩ :=
    HirschCircuitLocalization.rowCircuitStep_exists_target_blocking_row a b x y hstep
  have hyzero : HirschCircuit.slack a b y j = 0 := by
    simp [HirschCircuit.slack, hjy]
  have hdown : HirschCircuit.slack a b y j < HirschCircuit.slack a b x j := by
    rw [hyzero]
    change 0 < b j - ⟪a j, x⟫
    have hpos := hjpos
    rwa [inner_sub_right, hjy] at hpos
  have hsvnonneg : ∀ i, 0 ≤ HirschCircuit.slack a b v i := by
    intro i
    exact sub_nonneg.mpr (hv.1 i)
  obtain ⟨hsvne, htrap⟩ := HirschCircuit.same_phase_zero_blocker_is_trapped_positive
    M (HirschCircuit.slack a b v) r (HirschCircuit.slack a b x) (HirschCircuit.slack a b y)
    hM hsvnonneg heqx heqy j hyzero hdown
  have hvstrict : ⟪a j, v⟫ < b j := by
    have hpos := lt_of_le_of_ne (hsvnonneg j) (Ne.symm hsvne)
    exact sub_pos.mp hpos
  have hdel := rowMap_rowsWithout_injective_of_slack_vertex a b j v hv hvstrict
  exact ⟨j, hja, hjy, hjpos, hvstrict, htrap, hdel,
    vertex_survives_rowsWithout_of_slack a b j v hv hvstrict⟩

/-- Any row slack at a vertex offers a strictly smaller pointed presentation
and a fresh explicit cubic circuit route to the SAME vertex target. This is a
circuit route in the relaxed outer, not an edge route or a reinsertion theorem. -/
theorem slack_row_has_lower_excess_target_preserving_cubic_outer
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (j : Fin n)
    (x v : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b)
    (hv : v ∈ extremePoints ℝ (Hpoly a b)) (hvstrict : ⟪a j, v⟫ < b j) :
    let m := Fintype.card {i : Fin n // i ≠ j}
    m < n ∧ m - d < n - d ∧
    Function.Injective (HirschCircuit.rowMap (rowsWithout a j)) ∧
    v ∈ extremePoints ℝ (Hpoly (rowsWithout a j) (rhsWithout b j)) ∧
    RowCircuitWalk (rowsWithout a j) (rhsWithout b j) (17 * m ^ 3) x v := by
  dsimp only
  have hdel := rowMap_rowsWithout_injective_of_slack_vertex a b j v hv hvstrict
  have hvdel := vertex_survives_rowsWithout_of_slack a b j v hv hvstrict
  have hcard := rowsWithout_card_lt j
  have hdim := HirschCircuitLocalization.rows_ge_dimension_of_injective (rowsWithout a j) hdel
  have hxdel : x ∈ Hpoly (rowsWithout a j) (rhsWithout b j) := by
    intro k
    exact hx (rowsWithoutEquiv j k).1
  refine ⟨hcard, by omega, hdel, hvdel, ?_⟩
  exact HirschCircuit.rowCircuitWalk_explicit_cubic_of_injective
    (rowsWithout a j) (rhsWithout b j) hdel x v hxdel hvdel

#print axioms rowMap_rowsWithout_not_injective_of_unique_nonneutral
#print axioms rowCircuit_pointed_deletion_iff_other_nonneutral
#print axioms vertex_survives_rowsWithout_of_slack
#print axioms rowMap_rowsWithout_injective_of_slack_vertex
#print axioms rowsWithout_card_lt
#print axioms rowCircuitStep_same_phase_has_target_preserving_pointed_deletion
#print axioms slack_row_has_lower_excess_target_preserving_cubic_outer

end HirschDeletion
