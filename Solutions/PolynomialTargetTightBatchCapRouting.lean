import Mathlib
import Solutions.PolynomialTargetAnchoredDeletion
import Solutions.PolynomialInjectiveHpolyVertexExistence
import Solutions.PolynomialCompactCapVertexClassification
import Solutions.PolynomialSimultaneousClipParentFaceRouting

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 7000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschTargetDeletion

/-- Rows strictly slack at the fixed vertex target. -/
def targetSlackRows
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) :=
  {i : Fin n // ⟪a i, v⟫ < b i}

noncomputable instance targetSlackRowsFintype
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) :
    Fintype (targetSlackRows a b v) := Fintype.ofFinite _

/-- If an injective finite H-presentation has exactly one old vertex `v`, then
any compactifying negative-row-sum cap placed strictly above `v` has ordinary
vertex-edge diameter at most two. Every genuinely new cap vertex is adjacent
to an old vertex, and the only possible old vertex is `v`. -/
theorem injective_single_vertex_cap_diamLE_two
    {d m : ℕ}
    (a : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (hverts : extremePoints ℝ (Hpoly a b) = {v})
    (M : ℝ) (hvM : HirschPointed.injectiveCapValue a v < M) :
    DiamLE (HirschPointed.injectiveCappedHpoly a b M) 2 := by
  classical
  let Q := Hpoly a b
  let c := HirschPointed.injectiveCapNormal a
  let R := HirschPointed.injectiveCappedHpoly a b M
  have hRbd : Bornology.IsBounded R :=
    HirschPointed.injectiveCappedHpoly_isBounded a b M hinj
  have hRc : IsClosed R := by
    change IsClosed (HirschPointed.injectiveCappedHpoly a b M)
    rw [HirschPointed.injectiveCappedHpoly_eq_inter]
    exact (HirschCapVertices.hpoly_isClosed a b).inter
      (isClosed_le (by fun_prop) continuous_const)
  have hRcompact : IsCompact R :=
    Metric.isCompact_iff_isClosed_bounded.2 ⟨hRc, hRbd⟩
  have hmodel : R = Q ∩ {x | ⟪c, x⟫ ≤ M} := by
    simpa [Q, c, R] using HirschPointed.injectiveCappedHpoly_eq_inter a b M
  have hcapCompact : IsCompact (Q ∩ {x | ⟪c, x⟫ ≤ M}) := by
    rw [← hmodel]
    exact hRcompact
  have hclass : ∀ z ∈ extremePoints ℝ R, z = v ∨ Adj R v z := by
    intro z hz
    have hzModel : z ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ M}) := by
      rw [← hmodel]
      exact hz
    rcases HirschCapVertices.compact_hpoly_cap_vertex_classification
        a b c M (by simpa [Q] using hcapCompact) z hzModel with hold | hnew
    · left
      have hzv : z ∈ ({v} : Set _) := by
        rw [← hverts]
        exact hold
      exact Set.mem_singleton_iff.mp hzv
    · right
      obtain ⟨_hzcap, w, hwOld, _hwbelow, hwz⟩ := hnew
      have hwv : w = v := by
        apply Set.mem_singleton_iff.mp
        rw [← hverts]
        exact hwOld
      subst w
      rw [← hmodel] at hwz
      exact hwz
  intro u hu z hz
  have huC := hclass u hu
  have hzC := hclass z hz
  have huV : u = v ∨ Adj R u v := by
    rcases huC with huv | huv
    · exact Or.inl huv
    · right
      exact ⟨huv.1.symm, by simpa [segment_symm] using huv.2⟩
  have hvZ : v = z ∨ Adj R v z := by
    rcases hzC with hzv | hzv
    · exact Or.inl hzv.symm
    · exact Or.inr hzv
  let w : ℕ → EuclideanSpace ℝ (Fin d) := fun k =>
    if k = 0 then u else if k = 1 then v else z
  refine ⟨w, by simp [w], by simp [w], ?_⟩
  intro j hj
  have hcases : j = 0 ∨ j = 1 := by omega
  rcases hcases with rfl | rfl
  · simpa [w] using huV
  · simpa [w] using hvZ

/-- Target-tight batch reinsertion with a constant-size compact-outer cost.

For a bounded parent and a fixed vertex target `v`, keep exactly the rows tight
at `v`. The resulting pointed outer has `v` as its unique old vertex. A far
negative-row-sum cap makes that outer compact; every new cap vertex is adjacent
to `v`, so the capped outer has graph diameter at most two. Restore ALL rows
strictly slack at `v` simultaneously. If the final exposed face of each restored
row has an ambient parent-edge route budget `B i`, then the original parent has
padded diameter at most `2 + sum_i B i`.

Thus the target-tight batch construction does not multiply an outer-diameter
recursion once per deleted row. The remaining cost is the additive family of
final parent-face route budgets. -/
theorem target_tight_batch_reinsertion_diamLE_of_parent_face_routes
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (B : targetSlackRows a b v → ℕ)
    (hFaces : ∀ i : targetSlackRows a b v,
      ∀ p ∈ extremePoints ℝ (Hpoly a b) ∩
          (Hpoly a b ∩ {z | ⟪a i.1, z⟫ = b i.1}),
      ∀ q ∈ extremePoints ℝ (Hpoly a b) ∩
          (Hpoly a b ∩ {z | ⟪a i.1, z⟫ = b i.1}),
        HirschRegionRoute.Route (Adj (Hpoly a b)) (B i) p q) :
    DiamLE (Hpoly a b) (2 + ∑ i, B i) := by
  classical
  obtain ⟨m, hm, e, hrange, hinj, hverts, _hzero⟩ :=
    exists_zero_diameter_target_outer a b v hv
  let ar : Fin m → EuclideanSpace ℝ (Fin d) := fun k => a (e k)
  let br : Fin m → ℝ := fun k => b (e k)
  let Q := Hpoly ar br
  let I := targetSlackRows a b v
  letI : Fintype I := by
    dsimp [I]
    infer_instance
  let ca : I → EuclideanSpace ℝ (Fin d) := fun i => a i.1
  let cb : I → ℝ := fun i => b i.1
  let P := Hpoly a b
  have hQclip : HirschRadial.clipSet Q ca cb = P := by
    ext z
    constructor
    · intro hz
      intro i
      by_cases hitight : ⟪a i, v⟫ = b i
      · obtain ⟨k, hk⟩ := (hrange i).2 hitight
        have hkz := hz.1 k
        simpa [ar, br, hk] using hkz
      · have hislack : ⟪a i, v⟫ < b i :=
          lt_of_le_of_ne (hv.1 i) hitight
        exact hz.2 ⟨i, hislack⟩
    · intro hz
      refine ⟨?_, ?_⟩
      · intro k
        exact hz (e k)
      · intro i
        exact hz i.1
  have hPc : IsCompact P := by
    have hclosed : IsClosed P := by
      simpa [P] using HirschCapVertices.hpoly_isClosed a b
    exact Metric.isCompact_iff_isClosed_bounded.2 ⟨hclosed, by simpa [P] using hbd⟩
  have hPne : P.Nonempty := ⟨v, hv.1⟩
  let c := HirschPointed.injectiveCapNormal ar
  obtain ⟨M, hPbelow, _hOldBelow⟩ :=
    HirschCapVertices.exists_level_above_compact_and_outer_vertices
      ar br P hPc hPne c
  let R := HirschPointed.injectiveCappedHpoly ar br M
  have hRbd : Bornology.IsBounded R :=
    HirschPointed.injectiveCappedHpoly_isBounded ar br M (by simpa [ar] using hinj)
  have hRc : IsClosed R := by
    change IsClosed (HirschPointed.injectiveCappedHpoly ar br M)
    rw [HirschPointed.injectiveCappedHpoly_eq_inter]
    exact (HirschCapVertices.hpoly_isClosed ar br).inter
      (isClosed_le (by fun_prop) continuous_const)
  have hRcompact : IsCompact R :=
    Metric.isCompact_iff_isClosed_bounded.2 ⟨hRc, hRbd⟩
  have hQconv : Convex ℝ Q := by
    simpa [Q] using HirschCapVertices.hpoly_convex ar br
  have hRconv : Convex ℝ R := by
    rw [show R = Q ∩ {x | ⟪c, x⟫ ≤ M} by
      simpa [R, Q, c] using HirschPointed.injectiveCappedHpoly_eq_inter ar br M]
    intro x hx y hy s t hs ht hst
    refine ⟨hQconv hx.1 hy.1 hs ht hst, ?_⟩
    change ⟪c, s • x + t • y⟫ ≤ M
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    have hsum : s * M + t * M = M := by rw [← add_mul, hst, one_mul]
    linarith [mul_le_mul_of_nonneg_left hx.2 hs,
      mul_le_mul_of_nonneg_left hy.2 ht]
  have hvCap : HirschPointed.injectiveCapValue ar v < M := by
    have h := hPbelow v hv.1
    simpa [c, HirschPointed.injectiveCapNormal_eval] using h
  have hRdiam : DiamLE R 2 := by
    apply injective_single_vertex_cap_diamLE_two ar br v (by simpa [ar] using hinj)
    · simpa [Q, ar, br] using hverts
    · exact hvCap
  have hvQ : v ∈ Q := by
    have hvQext : v ∈ extremePoints ℝ Q := by
      rw [show extremePoints ℝ Q = {v} by simpa [Q, ar, br] using hverts]
      exact Set.mem_singleton v
    exact hvQext.1
  have hvR : v ∈ R := ⟨hvQ, hvCap.le⟩
  have hFinal : HirschRadial.clipSet R ca cb = P := by
    ext z
    constructor
    · intro hz
      have hzQ : z ∈ Q := hz.1.1
      have hzCuts : ∀ i, ⟪ca i, z⟫ ≤ cb i := hz.2
      rw [← hQclip]
      exact ⟨hzQ, hzCuts⟩
    · intro hzP
      have hzQCuts : z ∈ HirschRadial.clipSet Q ca cb := by
        rw [hQclip]
        exact hzP
      refine ⟨⟨hzQCuts.1, ?_⟩, hzQCuts.2⟩
      have hcap := hPbelow z hzP
      simpa [c, HirschPointed.injectiveCapNormal_eval] using hcap.le
  have hstrict : ∀ i : I, ⟪ca i, v⟫ < cb i := by
    intro i
    exact i.2
  have hFaces' : ∀ i : I,
      ∀ p ∈ extremePoints ℝ (HirschRadial.clipSet R ca cb) ∩
          (HirschRadial.clipSet R ca cb ∩ {z | ⟪ca i, z⟫ = cb i}),
      ∀ q ∈ extremePoints ℝ (HirschRadial.clipSet R ca cb) ∩
          (HirschRadial.clipSet R ca cb ∩ {z | ⟪ca i, z⟫ = cb i}),
        HirschRegionRoute.Route (Adj (HirschRadial.clipSet R ca cb)) (B i) p q := by
    intro i p hp q hq
    have hp' := hp
    have hq' := hq
    rw [hFinal] at hp' hq'
    have h := hFaces i p (by simpa [ca, cb, P] using hp') q
      (by simpa [ca, cb, P] using hq')
    simpa [hFinal] using h
  have hres := HirschRadial.diamLE_clip_of_strict_centre_with_parent_face_routes
    R hRcompact hRconv ca cb 2 B hRdiam hFaces' v hvR hstrict
  rw [hFinal] at hres
  exact hres

#print axioms injective_single_vertex_cap_diamLE_two
#print axioms target_tight_batch_reinsertion_diamLE_of_parent_face_routes

end HirschTargetDeletion
