import Mathlib
import Solutions.PolynomialVertexSpan
import Solutions.PolynomialCircuitStepProgress
import Solutions.CircuitPhaseBlockerPersistence
import Solutions.PolynomialOneRowDeletionCubicCircuitWalk

/-!
Target-anchored simultaneous row deletion.

Retaining every row tight at a fixed original vertex preserves that vertex and
pointedness, even after a whole batch of slack rows is deleted. Retaining exactly
the tight rows produces a possibly unbounded outer with that vertex as its only
vertex. None of these statements bounds the cost of restoring the deleted cuts.
-/

open scoped RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschTargetDeletion

/-- Covering the rows tight at one original vertex is enough for injectivity.
No ambient boundedness or circuit hypothesis is needed. -/
theorem selected_rowMap_injective_of_covers_target_tight
    {d n m : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (e : Fin m → Fin n)
    (hcover : ∀ i, ⟪a i, v⟫ = b i → ∃ k, e k = i) :
    Function.Injective (HirschCircuit.rowMap (fun k => a (e k))) := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply HirschPolynomialAccess.vertex_tight_rows_span_checked d n a b v hv (p - q)
  intro i hi
  obtain ⟨k, hk⟩ := hcover i hi
  have h := congrFun hpq k
  change ⟪a (e k), p⟫ = ⟪a (e k), q⟫ at h
  rw [hk] at h
  rw [inner_sub_right, h, sub_self]

/-- Retaining all target-tight inequalities preserves the target as an actual
vertex of the relaxed outer, not merely as a feasible point. -/
theorem selected_vertex_of_covers_target_tight
    {d n m : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (e : Fin m → Fin n)
    (hcover : ∀ i, ⟪a i, v⟫ = b i → ∃ k, e k = i) :
    v ∈ extremePoints ℝ (Hpoly (fun k => a (e k)) (fun k => b (e k))) := by
  refine ⟨fun k => hv.1 (e k), ?_⟩
  intro p hp q hq hseg
  obtain ⟨α, β, hα, hβ, hsum, hcomb⟩ := hseg
  apply sub_eq_zero.mp
  apply HirschPolynomialAccess.vertex_tight_rows_span_checked d n a b v hv (p - v)
  intro i hi
  obtain ⟨k, hk⟩ := hcover i hi
  have hp_le : ⟪a i, p⟫ ≤ b i := by simpa only [hk] using hp k
  have hq_le : ⟪a i, q⟫ ≤ b i := by simpa only [hk] using hq k
  have heval := congrArg (fun z : EuclideanSpace ℝ (Fin d) => ⟪a i, z⟫) hcomb
  simp only [inner_add_right, inner_smul_right] at heval
  have hb : α * b i + β * b i = b i := by
    rw [← add_mul, hsum, one_mul]
  have hp_eq : ⟪a i, p⟫ = b i := by
    by_contra hne
    have hlt : ⟪a i, p⟫ < b i := lt_of_le_of_ne hp_le hne
    have h1 := mul_lt_mul_of_pos_left hlt hα
    have h2 := mul_le_mul_of_nonneg_left hq_le hβ.le
    rw [hi] at heval
    linarith
  rw [inner_sub_right, hp_eq, hi, sub_self]

/-- Any finite batch of rows strictly slack at the target can be deleted at
once. The retained presentation has exactly `n - |J|` rows, remains pointed,
keeps the same target vertex, and recovers the original set when J is restored.
The source and the other original vertices need not survive as vertices. -/
theorem exists_target_preserving_batch_deletion
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (J : Finset (Fin n))
    (hJ : ∀ i ∈ J, ⟪a i, v⟫ < b i) :
    ∃ m : ℕ, m + J.card = n ∧ ∃ e : Fin m ↪ Fin n,
      (∀ i, (∃ k, e k = i) ↔ i ∉ J) ∧
      Function.Injective (HirschCircuit.rowMap (fun k => a (e k))) ∧
      v ∈ extremePoints ℝ (Hpoly (fun k => a (e k)) (fun k => b (e k))) ∧
      (Hpoly (fun k => a (e k)) (fun k => b (e k)) ∩
        {z | ∀ i ∈ J, ⟪a i, z⟫ ≤ b i} = Hpoly a b) := by
  classical
  let I := {i : Fin n // i ∉ J}
  let m := Fintype.card I
  let φ : Fin m ≃ I := (Fintype.equivFin I).symm
  let e : Fin m ↪ Fin n :=
    ⟨fun k => (φ k).1, fun p q h => φ.injective (Subtype.ext h)⟩
  have hcard : m = n - J.card := by
    dsimp [m, I]
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_subtype_compl (fun i : Fin n => i ∈ J)
  have hJn : J.card ≤ n := by simpa only [Fintype.card_fin] using J.card_le_univ
  have hcount : m + J.card = n := by omega
  have hret : ∀ i, (∃ k, e k = i) ↔ i ∉ J := by
    intro i
    constructor
    · rintro ⟨k, rfl⟩
      exact (φ k).2
    · intro hi
      refine ⟨φ.symm ⟨i, hi⟩, ?_⟩
      simp [e]
  have hcover : ∀ i, ⟪a i, v⟫ = b i → ∃ k, e k = i := by
    intro i hi
    apply (hret i).2
    intro hiJ
    have hlt := hJ i hiJ
    rw [hi] at hlt
    exact (lt_irrefl _ hlt)
  refine ⟨m, hcount, e, hret,
    selected_rowMap_injective_of_covers_target_tight a b v hv e hcover,
    selected_vertex_of_covers_target_tight a b v hv e hcover, ?_⟩
  ext z
  constructor
  · rintro ⟨hQ, hD⟩ i
    by_cases hi : i ∈ J
    · exact hD i hi
    · obtain ⟨k, hk⟩ := (hret i).2 hi
      simpa only [hk] using hQ k
  · intro hz
    exact ⟨fun k => hz (e k), fun i _ => hz i⟩

/-- If the retained rows are exactly target-tight rows, the relaxed outer has
no other vertex. It may still contain infinitely many nonvertex points. -/
theorem selected_tight_outer_extremePoints_eq_singleton
    {d n m : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (e : Fin m → Fin n)
    (hcover : ∀ i, ⟪a i, v⟫ = b i → ∃ k, e k = i)
    (htight : ∀ k, ⟪a (e k), v⟫ = b (e k)) :
    extremePoints ℝ (Hpoly (fun k => a (e k)) (fun k => b (e k))) = {v} := by
  ext z
  constructor
  · intro hz
    apply Set.mem_singleton_iff.mpr
    apply sub_eq_zero.mp
    apply HirschPolynomialAccess.vertex_tight_rows_span_checked d m
      (fun k => a (e k)) (fun k => b (e k)) z hz (z - v)
    intro k hk
    change ⟪a (e k), z - v⟫ = 0
    rw [inner_sub_right, hk, htight k, sub_self]
  · intro hz
    have hzv : z = v := Set.mem_singleton_iff.mp hz
    subst z
    exact selected_vertex_of_covers_target_tight a b v hv e hcover

/-- The old-vertex graph of the exact target-tight outer has diameter zero.
This does not make the original clipped polyhedron's graph diameter zero. -/
theorem selected_tight_outer_diamLE_zero
    {d n m : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (e : Fin m → Fin n)
    (hcover : ∀ i, ⟪a i, v⟫ = b i → ∃ k, e k = i)
    (htight : ∀ k, ⟪a (e k), v⟫ = b (e k)) :
    DiamLE (Hpoly (fun k => a (e k)) (fun k => b (e k))) 0 := by
  have hverts := selected_tight_outer_extremePoints_eq_singleton a b v hv e hcover htight
  intro p hp q hq
  rw [hverts] at hp hq
  have hpv : p = v := Set.mem_singleton_iff.mp hp
  have hqv : q = v := Set.mem_singleton_iff.mp hq
  subst p
  subst q
  exact ⟨fun _ => v, rfl, rfl, by intro j hj; omega⟩

/-- Every original vertex admits a target-tight pointed outer with that vertex
as its sole vertex. All omitted inequalities are strictly slack at the target.
This offers a zero-old-vertex-cost batch deletion, leaving the cost of restoring
all omitted cuts as the genuine remaining problem. -/
theorem exists_zero_diameter_target_outer
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    ∃ m : ℕ, m ≤ n ∧ ∃ e : Fin m ↪ Fin n,
      (∀ i, (∃ k, e k = i) ↔ ⟪a i, v⟫ = b i) ∧
      Function.Injective (HirschCircuit.rowMap (fun k => a (e k))) ∧
      extremePoints ℝ (Hpoly (fun k => a (e k)) (fun k => b (e k))) = {v} ∧
      DiamLE (Hpoly (fun k => a (e k)) (fun k => b (e k))) 0 := by
  classical
  let J : Finset (Fin n) := Finset.univ.filter (fun i => ⟪a i, v⟫ < b i)
  have hJ : ∀ i ∈ J, ⟪a i, v⟫ < b i := fun i hi => (Finset.mem_filter.mp hi).2
  obtain ⟨m, hcount, e, hret, hinj, _hv', _hrecover⟩ :=
    exists_target_preserving_batch_deletion a b v hv J hJ
  have hrange : ∀ i, (∃ k, e k = i) ↔ ⟪a i, v⟫ = b i := by
    intro i
    rw [hret i]
    constructor
    · intro hi
      by_contra hne
      exact hi (Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, lt_of_le_of_ne (hv.1 i) hne⟩)
    · intro hi hiJ
      have hlt := hJ i hiJ
      rw [hi] at hlt
      exact (lt_irrefl _ hlt)
  have hcover : ∀ i, ⟪a i, v⟫ = b i → ∃ k, e k = i := fun i => (hrange i).2
  have htight : ∀ k, ⟪a (e k), v⟫ = b (e k) := fun k => (hrange (e k)).1 ⟨k, rfl⟩
  exact ⟨m, by omega, e, hrange, hinj,
    selected_tight_outer_extremePoints_eq_singleton a b v hv e hcover htight,
    selected_tight_outer_diamLE_zero a b v hv e hcover htight⟩

/-- A same-phase blocker for a vertex target always has a pointed deletion
that preserves that target vertex. Thus #163's universal-vertex-face exception
cannot occur in the actual same-phase-to-vertex application. The source may be
nonvertex, and the parent may be unbounded. -/
theorem same_phase_step_has_target_preserving_blocker_deletion
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hstep : RowCircuitStep a b x y)
    (M : ℝ) (hM : 0 ≤ M) (r : Fin n → ℝ)
    (heqx : HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v) r =
      HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v) (HirschCircuit.slack a b x))
    (heqy : HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v) r =
      HirschCircuit.phaseProgressSet M (HirschCircuit.slack a b v) (HirschCircuit.slack a b y)) :
    ∃ j : Fin n,
      a j ≠ 0 ∧ ⟪a j, y⟫ = b j ∧ 0 < ⟪a j, y - x⟫ ∧
      ⟪a j, v⟫ < b j ∧
      Function.Injective (HirschCircuit.rowMap (HirschDeletion.rowsWithout a j)) ∧
      v ∈ extremePoints ℝ
        (Hpoly (HirschDeletion.rowsWithout a j) (HirschDeletion.rhsWithout b j)) := by
  classical
  obtain ⟨j, hja, hjy, hjpos⟩ :=
    HirschCircuitLocalization.rowCircuitStep_exists_target_blocking_row a b x y hstep
  have hsy : HirschCircuit.slack a b y j = 0 := by simp [HirschCircuit.slack, hjy]
  have hdown : HirschCircuit.slack a b y j < HirschCircuit.slack a b x j := by
    rw [hsy]
    rw [inner_sub_right, hjy] at hjpos
    simpa [HirschCircuit.slack] using hjpos
  have hvnonneg : ∀ i, 0 ≤ HirschCircuit.slack a b v i := by
    intro i
    exact sub_nonneg.mpr (hv.1 i)
  obtain ⟨hvne, _htrap⟩ := HirschCircuit.same_phase_zero_blocker_is_trapped_positive
    M (HirschCircuit.slack a b v) r
      (HirschCircuit.slack a b x) (HirschCircuit.slack a b y)
    hM hvnonneg heqx heqy j hsy hdown
  have hvpos : 0 < HirschCircuit.slack a b v j :=
    lt_of_le_of_ne (hvnonneg j) (Ne.symm hvne)
  have hjv : ⟪a j, v⟫ < b j := sub_pos.mp hvpos
  let e : Fin (Fintype.card {i : Fin n // i ≠ j}) → Fin n :=
    fun k => (HirschDeletion.rowsWithoutEquiv j k).1
  have hcover : ∀ i, ⟪a i, v⟫ = b i → ∃ k, e k = i := by
    intro i hi
    have hij : i ≠ j := by
      intro heq
      subst i
      rw [hi] at hjv
      exact (lt_irrefl _ hjv)
    refine ⟨(HirschDeletion.rowsWithoutEquiv j).symm ⟨i, hij⟩, ?_⟩
    simp [e]
  refine ⟨j, hja, hjy, hjpos, hjv, ?_, ?_⟩
  · simpa only [HirschDeletion.rowsWithout, e] using
      selected_rowMap_injective_of_covers_target_tight a b v hv e hcover
  · simpa only [HirschDeletion.rowsWithout, HirschDeletion.rhsWithout, e] using
      selected_vertex_of_covers_target_tight a b v hv e hcover

#print axioms selected_rowMap_injective_of_covers_target_tight
#print axioms selected_vertex_of_covers_target_tight
#print axioms exists_target_preserving_batch_deletion
#print axioms selected_tight_outer_extremePoints_eq_singleton
#print axioms selected_tight_outer_diamLE_zero
#print axioms exists_zero_diameter_target_outer
#print axioms same_phase_step_has_target_preserving_blocker_deletion

end HirschTargetDeletion
