import Mathlib
import Solutions.PolynomialInjectiveFacePortals
import Solutions.PolynomialIntervalRegionRouting

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 6000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschPointed

open HirschPolynomialAccess HirschRegionRoute

/-- A feasible common-carrier sequence in an injective H-polyhedron can be
assembled from arbitrary local ambient parent-edge route budgets.

The circuit checkpoints themselves need not be vertices.  Consecutive common
carriers meet at the shared checkpoint, and the injective face-portal theorem
replaces that nonvertex overlap by a genuine parent vertex in the intersection.
The existing region graph then charges each carrier occurrence once. -/
theorem route_of_feasible_commonFace_parent_routes_of_rowMap_injective
    {d n L : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (HirschCircuit.rowMap a))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hfeas : ∀ k ≤ L, w k ∈ Hpoly a b)
    (h0 : w 0 ∈ extremePoints ℝ (Hpoly a b))
    (hL : w L ∈ extremePoints ℝ (Hpoly a b))
    (B : Fin L → ℕ)
    (hlocal : ∀ i : Fin L,
      ∀ u ∈ extremePoints ℝ (Hpoly a b) ∩
          commonFace a b (w i.val) (w (i.val + 1)),
      ∀ v ∈ extremePoints ℝ (Hpoly a b) ∩
          commonFace a b (w i.val) (w (i.val + 1)),
        Route (Adj (Hpoly a b)) (B i) u v) :
    Route (Adj (Hpoly a b)) (∑ i, B i) (w 0) (w L) := by
  classical
  by_cases hzero : L = 0
  · subst L
    simpa using (show Route (Adj (Hpoly a b)) 0 (w 0) (w 0) from
      ⟨fun _ => w 0, rfl, rfl, by intro j hj; omega⟩)
  have hpos : 0 < L := Nat.pos_of_ne_zero hzero
  let F : Fin L → Set (EuclideanSpace ℝ (Fin d)) := fun i =>
    commonFace a b (w i.val) (w (i.val + 1))
  let S : Fin L → Set (EuclideanSpace ℝ (Fin d)) := fun i =>
    extremePoints ℝ (Hpoly a b) ∩ F i
  let s : Fin L → ℕ := fun i => i.val
  let t : Fin L → ℕ := fun i => i.val + 1
  have hportal : ∀ i j, s i ≤ t j → s j ≤ t i →
      ∃ z, z ∈ S i ∧ z ∈ S j := by
    intro i j hij hji
    by_cases heq : i = j
    · subst j
      have hiF : w i.val ∈ F i := by
        change w i.val ∈ commonFace a b (w i.val) (w (i.val + 1))
        exact commonFace_u_mem a b _ _ (hfeas i.val (by omega))
      obtain ⟨z, hzP, hzF⟩ :=
        commonFace_has_parent_vertex_of_rowMap_injective
          a b (w i.val) (w (i.val + 1)) (w i.val) hinj hiF
      exact ⟨z, ⟨hzP, hzF⟩, ⟨hzP, hzF⟩⟩
    have hnear : i.val + 1 = j.val ∨ j.val + 1 = i.val := by
      dsimp [s, t] at hij hji
      have hval : i.val ≠ j.val := by
        intro h
        apply heq
        exact Fin.ext h
      omega
    rcases hnear with hnext | hprev
    · have hz1 : w (i.val + 1) ∈ F i := by
        change w (i.val + 1) ∈ commonFace a b (w i.val) (w (i.val + 1))
        exact commonFace_x_mem a b _ _ (hfeas (i.val + 1) (by omega))
      have hz2 : w (i.val + 1) ∈ F j := by
        change w (i.val + 1) ∈ commonFace a b (w j.val) (w (j.val + 1))
        have h := commonFace_u_mem a b (w j.val) (w (j.val + 1))
          (hfeas j.val (by omega))
        simpa [hnext] using h
      obtain ⟨z, hzP, hzFi, hzFj⟩ :=
        commonFaces_shared_parent_vertex_of_rowMap_injective
          a b (w i.val) (w (i.val + 1)) (w j.val) (w (j.val + 1))
          (w (i.val + 1)) hinj hz1 hz2
      exact ⟨z, ⟨hzP, hzFi⟩, ⟨hzP, hzFj⟩⟩
    · have hz1 : w (j.val + 1) ∈ F i := by
        change w (j.val + 1) ∈ commonFace a b (w i.val) (w (i.val + 1))
        have h := commonFace_u_mem a b (w i.val) (w (i.val + 1))
          (hfeas i.val (by omega))
        simpa [hprev] using h
      have hz2 : w (j.val + 1) ∈ F j := by
        change w (j.val + 1) ∈ commonFace a b (w j.val) (w (j.val + 1))
        exact commonFace_x_mem a b _ _ (hfeas (j.val + 1) (by omega))
      obtain ⟨z, hzP, hzFi, hzFj⟩ :=
        commonFaces_shared_parent_vertex_of_rowMap_injective
          a b (w i.val) (w (i.val + 1)) (w j.val) (w (j.val + 1))
          (w (j.val + 1)) hinj hz1 hz2
      exact ⟨z, ⟨hzP, hzFi⟩, ⟨hzP, hzFj⟩⟩
  have hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i := by
    intro k hk
    refine ⟨⟨k, hk⟩, ?_, ?_⟩
    · rfl
    · rfl
  let i0 : Fin L := ⟨0, hpos⟩
  let iL : Fin L := ⟨L - 1, by omega⟩
  have hreach : Nonempty ((intersectionGraph S).Walk i0 iL) := by
    apply region_walk_of_interval_cover S s t hportal L hcover i0 iL
    · dsimp [s, t, i0]
      omega
    · dsimp [s, t, iL]
      omega
  have hu : w 0 ∈ S i0 := by
    refine ⟨h0, ?_⟩
    change w 0 ∈ commonFace a b (w 0) (w (0 + 1))
    exact commonFace_u_mem a b _ _ (hfeas 0 (by omega))
  have hv : w L ∈ S iL := by
    refine ⟨hL, ?_⟩
    change w L ∈ commonFace a b (w (L - 1)) (w (L - 1 + 1))
    have h := commonFace_x_mem a b (w (L - 1)) (w (L - 1 + 1))
      (hfeas (L - 1 + 1) (by omega))
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ L)] using h
  have hlocal' : ∀ i,
      ∀ u ∈ S i, ∀ v ∈ S i,
        Route (Adj (Hpoly a b)) (B i) u v := by
    intro i u hu' v hv'
    exact hlocal i u (by simpa [S, F] using hu') v (by simpa [S, F] using hv')
  exact route_of_connected_regions (Adj (Hpoly a b)) S B hlocal'
    hreach (w 0) (w L) hu hv

#print axioms route_of_feasible_commonFace_parent_routes_of_rowMap_injective

end HirschPointed
