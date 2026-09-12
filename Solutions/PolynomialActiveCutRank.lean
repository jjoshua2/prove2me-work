import Solutions.PolynomialExcessFaceRank

/-!
# At a clipped vertex, cut rank controls free parent-face dimension

New proof candidate; not yet compiled in the pinned workspace.
This statement is not specific to feedback boxes. An ordinary H-polyhedron
vertex has no nonzero direction annihilating all its active rows. Therefore
cut evaluation is injective on any direction space already annihilated by
the active non-cut rows. Counting rank, rather than the number of cut labels,
is the resource used by the accompanying monotone-anchor routing proof.
-/
open scoped RealInnerProductSpace
open Set Hirsch HirschPolynomialAccess
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace HirschCutRank

variable {d n : ℕ}

/-- Cut evaluation is injective on the free parent-face direction space. -/
theorem cut_eval_injective_on_parent_directions
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (cuts : Finset (Fin n)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hparent : ∀ i, i ∉ cuts → ⟪a i, x⟫ = b i →
      ∀ z ∈ W, ⟪a i, z⟫ = 0) :
    Function.Injective ((rowEvalMap a cuts).domRestrict W) := by
  classical
  let T := (rowEvalMap a cuts).domRestrict W
  intro y z hyz
  apply Subtype.ext
  let q : W := y - z
  have hTq : T q = 0 := by
    dsimp [q]
    rw [map_sub, hyz, sub_self]
  have horth : ∀ i, ⟪a i, x⟫ = b i →
      ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
    intro i hi
    by_cases hic : i ∈ cuts
    · have h := congrFun hTq ⟨i, hic⟩
      exact h
    · exact hparent i hic hi q q.property
  have hzero := vertex_tight_rows_span_checked d n a b x hx q horth
  change (y : EuclideanSpace ℝ (Fin d)) - (z : EuclideanSpace ℝ (Fin d)) = 0 at hzero
  exact sub_eq_zero.mp hzero

/-- Exact restricted rank, including zero-dimensional and degenerate cases. -/
theorem restricted_cut_rank_eq_parent_direction_dim
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (cuts : Finset (Fin n)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hparent : ∀ i, i ∉ cuts → ⟪a i, x⟫ = b i →
      ∀ z ∈ W, ⟪a i, z⟫ = 0) :
    Module.finrank ℝ (((rowEvalMap a cuts).domRestrict W).range) =
      Module.finrank ℝ W := by
  let T := (rowEvalMap a cuts).domRestrict W
  have hinj : Function.Injective T :=
    cut_eval_injective_on_parent_directions a b x hx cuts W hparent
  have hnull := T.finrank_range_add_finrank_ker
  rw [LinearMap.ker_eq_bot.mpr hinj] at hnull
  simpa [T] using hnull

/-- The bound is ambient cut rank, not cut cardinality. -/
theorem parent_direction_dim_le_cut_rank
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (cuts : Finset (Fin n)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hparent : ∀ i, i ∉ cuts → ⟪a i, x⟫ = b i →
      ∀ z ∈ W, ⟪a i, z⟫ = 0) :
    Module.finrank ℝ W ≤ Module.finrank ℝ (rowEvalMap a cuts).range := by
  let R := rowEvalMap a cuts
  let T : W →ₗ[ℝ] R.range := R.rangeRestrict.comp W.subtype
  have hinj : Function.Injective T := by
    intro y z h
    apply cut_eval_injective_on_parent_directions a b x hx cuts W hparent
    exact congrArg Subtype.val h
  exact LinearMap.finrank_le_finrank_of_injective hinj

/-- Only cuts active at this particular endpoint need to be evaluated. -/
theorem active_restricted_cut_rank_eq_parent_direction_dim
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (cuts : Finset (Fin n)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hparent : ∀ i, i ∉ cuts → ⟪a i, x⟫ = b i →
      ∀ z ∈ W, ⟪a i, z⟫ = 0) :
    Module.finrank ℝ
      (((rowEvalMap a (cuts.filter (fun i => ⟪a i, x⟫ = b i))).domRestrict W).range) =
      Module.finrank ℝ W := by
  classical
  apply restricted_cut_rank_eq_parent_direction_dim a b x hx
  intro i hi hit z hz
  have hnot : i ∉ cuts := by
    intro hic
    exact hi (Finset.mem_filter.mpr ⟨hic, hit⟩)
  exact hparent i hnot hit z hz

#print axioms cut_eval_injective_on_parent_directions
#print axioms restricted_cut_rank_eq_parent_direction_dim
#print axioms parent_direction_dim_le_cut_rank
#print axioms active_restricted_cut_rank_eq_parent_direction_dim
end HirschCutRank
