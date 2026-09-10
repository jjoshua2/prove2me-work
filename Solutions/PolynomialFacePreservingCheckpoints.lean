import Solutions.PolynomialIntervalStartPortals
import Mathlib.Analysis.Convex.KreinMilman

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRegionRoute

/-- A nonempty closed extreme subset of a compact parent contains a parent
extreme vertex. The given point need not itself be a vertex. -/
theorem compact_face_point_has_parent_vertex
    {d : ℕ} (P F : Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P) (hF : IsExtreme ℝ P F) (hclosed : IsClosed F)
    (hne : F.Nonempty) :
    ∃ v, v ∈ extremePoints ℝ P ∧ v ∈ F := by
  obtain ⟨v, hv⟩ :=
    (hP.of_isClosed_subset hclosed hF.subset).extremePoints_nonempty hne
  exact ⟨v, hF.extremePoints_subset_extremePoints hv, hv.1⟩

/-- All closed parent extreme faces containing a feasible point can be
preserved simultaneously by one parent vertex. No finiteness assumption on
the face family is necessary. This is an incidence selector, not a continuous
map, a nearest-vertex map, or a claim that a circuit step is an edge. -/
theorem exists_vertex_preserving_face_memberships
    {d : ℕ} {ι : Type*} (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ P) :
    ∃ v, v ∈ extremePoints ℝ P ∧ ∀ i, x ∈ F i → v ∈ F i := by
  let G : Set (EuclideanSpace ℝ (Fin d)) :=
    P ∩ ⋂ i, ⋂ (_ : x ∈ F i), F i
  have hGc : IsClosed G :=
    hP.isClosed.inter (isClosed_iInter fun i => isClosed_iInter fun _ => hclosed i)
  have hxG : x ∈ G :=
    ⟨hx, mem_iInter.mpr fun i => mem_iInter.mpr fun hi => hi⟩
  have hGe : IsExtreme ℝ P G := by
    refine ⟨fun _ hz => hz.1, ?_⟩
    intro a ha b hb z hz hseg
    refine ⟨ha, mem_iInter.mpr fun i => mem_iInter.mpr fun hi => ?_⟩
    exact (hF i).left_mem_of_mem_openSegment ha hb
      (mem_iInter.mp (mem_iInter.mp hz.2 i) hi) hseg
  obtain ⟨v, hv, hvG⟩ := compact_face_point_has_parent_vertex P G hP hGe hGc ⟨x, hxG⟩
  exact ⟨v, hv, fun i hi => mem_iInter.mp (mem_iInter.mp hvG.2 i) hi⟩

/-- A single face-membership-preserving vertex selection fixes every parent
vertex. It may be discontinuous and need not preserve adjacency. -/
theorem face_preserving_vertex_selection
    {d : ℕ} {ι : Type*} (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i)) :
    ∃ r : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      (∀ x ∈ P, r x ∈ extremePoints ℝ P) ∧
      (∀ x ∈ extremePoints ℝ P, r x = x) ∧
      (∀ i x, x ∈ F i → r x ∈ F i) := by
  classical
  have hchoice : ∀ x : EuclideanSpace ℝ (Fin d), ∃ v,
      (x ∈ P → v ∈ extremePoints ℝ P) ∧
      (x ∈ extremePoints ℝ P → v = x) ∧
      (∀ i, x ∈ F i → v ∈ F i) := by
    intro x
    by_cases hxv : x ∈ extremePoints ℝ P
    · exact ⟨x, fun _ => hxv, fun _ => rfl, fun _ hi => hi⟩
    · by_cases hx : x ∈ P
      · obtain ⟨v, hv, hmem⟩ :=
          exists_vertex_preserving_face_memberships P F hP hF hclosed x hx
        exact ⟨v, fun _ => hv, fun h => False.elim (hxv h), hmem⟩
      · exact ⟨x, fun h => False.elim (hx h), fun _ => rfl, fun _ hi => hi⟩
  choose r hr using hchoice
  exact ⟨r, fun x hx => (hr x).1 hx, fun x hx => (hr x).2.1 hx,
    fun i x hx => (hr x).2.2 i hx⟩

/-- Geometric overlap of closed faces of a compact parent supplies a genuine
parent-vertex portal, even when the overlap witness is nonvertex. -/
theorem compact_faces_shared_point_portal
    {d : ℕ} (P F G : Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P) (hF : IsExtreme ℝ P F) (hG : IsExtreme ℝ P G)
    (hFc : IsClosed F) (hGc : IsClosed G)
    (x : EuclideanSpace ℝ (Fin d)) (hxF : x ∈ F) (hxG : x ∈ G) :
    ∃ v, v ∈ extremePoints ℝ P ∧ v ∈ F ∧ v ∈ G := by
  obtain ⟨v, hv, hvFG⟩ := compact_face_point_has_parent_vertex
    P (F ∩ G) hP (hF.inter hG) (hFc.inter hGc) ⟨x, hxF, hxG⟩
  exact ⟨v, hv, hvFG.1, hvFG.2⟩

/-- A fixed feasible face-covered sequence needs vertex endpoints only.
Interior checkpoints are rounded simultaneously, preserving every available
face incidence and charging each face once. The actual face budgets remain
explicit hypotheses. -/
theorem route_of_feasible_face_covered_sequence
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hfeas : ∀ k ≤ L, w k ∈ P)
    (h0 : w 0 ∈ extremePoints ℝ P) (hL : w L ∈ extremePoints ℝ P)
    (hcover : ∀ k < L, ∃ i, w k ∈ F i ∧ w (k + 1) ∈ F i) :
    Route (Adj P) (∑ i, B i) (w 0) (w L) := by
  obtain ⟨r, hrP, hrfix, hrF⟩ := face_preserving_vertex_selection P F hP hF hclosed
  have hroute := route_of_face_covered_sequence P F B hF hD (fun k => r (w k)) L
    (fun k hk => hrP (w k) (hfeas k hk)) (by
      intro k hk
      obtain ⟨i, hi, hi'⟩ := hcover k hk
      exact ⟨i, hrF i (w k) hi, hrF i (w (k + 1)) hi'⟩)
  simpa only [hrfix (w 0) h0, hrfix (w L) hL] using hroute

/-- PR #48 start containment with feasible, possibly nonvertex marked
checkpoints. Membership in the closed parent faces supplies feasibility.
Only the two route endpoints must already be parent vertices. Unmarked
interiors of the old sequence need not be feasible. -/
theorem route_of_face_interval_cover_of_feasible_start_containment
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (s t : ι → ℕ) (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hbound : ∀ i, t i ≤ L)
    (h0 : w 0 ∈ extremePoints ℝ P) (hL : w L ∈ extremePoints ℝ P)
    (hends : ∀ i, w (s i) ∈ F i ∧ w (t i) ∈ F i)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hcontain : ∀ i j, s i ≤ s j → s j ≤ t i → w (s j) ∈ F i) :
    Route (Adj P) (∑ i, B i) (w 0) (w L) := by
  obtain ⟨r, hrP, hrfix, hrF⟩ := face_preserving_vertex_selection P F hP hF hclosed
  have hroute := route_of_face_interval_cover_of_start_containment
    P F B hF hD s t (fun k => r (w k)) L hbound
    (fun i => ⟨hrP (w (s i)) ((hF i).subset (hends i).1),
      hrP (w (t i)) ((hF i).subset (hends i).2)⟩)
    (fun i => ⟨hrF i (w (s i)) (hends i).1, hrF i (w (t i)) (hends i).2⟩)
    hcover (fun i j hs ht => hrF i (w (s j)) (hcontain i j hs ht))
  simpa only [hrfix (w 0) h0, hrfix (w L) hL] using hroute

/-- The active-containment corollary likewise needs no intermediate vertex
hypothesis. This does not assert that an evolving polytope's faces have
nonempty intersections in the fixed parent, or that their costs are small. -/
theorem route_of_face_interval_cover_of_feasible_active_containment
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (s t : ι → ℕ) (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hvalid : ∀ i, s i ≤ t i) (hbound : ∀ i, t i ≤ L)
    (h0 : w 0 ∈ extremePoints ℝ P) (hL : w L ∈ extremePoints ℝ P)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hactive : ∀ i k, s i ≤ k → k ≤ t i → w k ∈ F i) :
    Route (Adj P) (∑ i, B i) (w 0) (w L) := by
  apply route_of_face_interval_cover_of_feasible_start_containment
    P F B hP hF hclosed hD s t w L hbound h0 hL
    (fun i => ⟨hactive i (s i) (Nat.le_refl _) (hvalid i),
      hactive i (t i) (hvalid i) (Nat.le_refl _)⟩) hcover
  intro i j hs ht
  exact hactive i (s j) hs ht

#print axioms compact_face_point_has_parent_vertex
#print axioms exists_vertex_preserving_face_memberships
#print axioms face_preserving_vertex_selection
#print axioms compact_faces_shared_point_portal
#print axioms route_of_feasible_face_covered_sequence
#print axioms route_of_face_interval_cover_of_feasible_start_containment
#print axioms route_of_face_interval_cover_of_feasible_active_containment

end HirschRegionRoute
