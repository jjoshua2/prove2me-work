import Mathlib
import Solutions.PolynomialUsedRegionRouting

/-!
# Path-preserving used-region routing

The support-sensitive routing theorem records which region labels are used, but
a bare list forgets the intersection witnesses connecting consecutive regions.
This module retains the actual simple intersection-graph path.

For closed extreme faces of a compact parent, the path is taken in the graph of
`extremePoints P ∩ F i`.  Consequently every path edge itself certifies a
shared **parent extreme vertex** in the two consecutive faces.  This is the
portal information needed by any later argument that wants pair-specific local
face costs instead of a whole-face diameter bound.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
namespace HirschRegionRoute

/-- Connected region routing while retaining the actual simple region path.
The route budget is exactly the cost sum on that path's support. -/
theorem route_of_connected_regions_with_used_path
    {V ι : Type*} [Fintype ι]
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, Route R (C i) u v)
    {i j : ι} (hreach : Nonempty ((intersectionGraph S).Walk i j))
    (u v : V) (hu : u ∈ S i) (hv : v ∈ S j) :
    ∃ p : (intersectionGraph S).Walk i j,
      p.IsPath ∧ Route R ((p.support.map C).sum) u v := by
  classical
  obtain ⟨walk⟩ := hreach
  let p := walk.toPath
  exact ⟨p.val, p.property,
    route_of_region_walk R S C hlocal p.val u hu v hv⟩

/-- Closed-face trace routing retaining a simple path in the intersection graph
of parent-vertex face regions.

For every edge of the returned path, unfolding `intersectionGraph` gives a
shared point in
`(extremePoints ℝ P ∩ F i) ∩ (extremePoints ℝ P ∩ F j)`.
Thus the graph edge is already a parent-vertex portal certificate, not merely a
nonvertex face-overlap witness. -/
theorem route_of_preconnected_face_cover_with_parent_routes_used_path
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i))
    (hlocal : ∀ i,
      ∀ u ∈ extremePoints ℝ P ∩ F i,
      ∀ v ∈ extremePoints ℝ P ∩ F i,
        Route (Adj P) (B i) u v)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsPreconnected K)
    (hcover : ∀ x ∈ K, ∃ i, x ∈ F i)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ P) (hv : v ∈ extremePoints ℝ P)
    (huK : u ∈ K) (hvK : v ∈ K) :
    ∃ i j : ι,
      u ∈ extremePoints ℝ P ∩ F i ∧
      v ∈ extremePoints ℝ P ∩ F j ∧
      ∃ p : (intersectionGraph (fun k => extremePoints ℝ P ∩ F k)).Walk i j,
        p.IsPath ∧ Route (Adj P) ((p.support.map B).sum) u v := by
  classical
  obtain ⟨i, hui⟩ := hcover u huK
  obtain ⟨j, hvj⟩ := hcover v hvK
  obtain ⟨faceWalk⟩ :=
    region_walk_of_preconnected_closed_cover
      F hclosed K hK hcover huK hvK i j hui hvj
  have hreach := face_walk_to_parent_vertex_walk P F hP hF hclosed faceWalk
  obtain ⟨p, hp, hr⟩ :=
    route_of_connected_regions_with_used_path
      (Adj P) (fun k => extremePoints ℝ P ∩ F k) B hlocal
      hreach u v ⟨hu, hui⟩ ⟨hv, hvj⟩
  exact ⟨i, j, ⟨hu, hui⟩, ⟨hv, hvj⟩, p, hp, hr⟩

/-- Every adjacency in a returned parent-vertex region path has an explicit
shared parent extreme vertex portal.  This is just the useful projection of the
`intersectionGraph` edge predicate. -/
theorem parent_vertex_portal_of_used_path_edge
    {d : ℕ} {ι : Type*}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    {i j : ι}
    (hij : (intersectionGraph (fun k => extremePoints ℝ P ∩ F k)).Adj i j) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ P ∧ z ∈ F i ∧ z ∈ F j := by
  obtain ⟨_hne, z, hzi, hzj⟩ := hij
  exact ⟨z, hzi.1, hzi.2, hzj.2⟩

#print axioms route_of_connected_regions_with_used_path
#print axioms route_of_preconnected_face_cover_with_parent_routes_used_path
#print axioms parent_vertex_portal_of_used_path_edge

end HirschRegionRoute
