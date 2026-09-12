import Mathlib
import Solutions.PolynomialRegionRouting
import Solutions.PolynomialParentRouteClosedFaceTrace

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace HirschRegionRoute

/-- Connected routing can expose the actual simple region-label support used
before the usual padding to every available label. The labels are distinct and
the route cost is exactly the sum of their mapped local costs. -/
theorem route_of_connected_regions_with_used_labels
    {V ι : Type*} [Fintype ι]
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, Route R (C i) u v)
    {i j : ι} (hreach : Nonempty ((intersectionGraph S).Walk i j))
    (u v : V) (hu : u ∈ S i) (hv : v ∈ S j) :
    ∃ l : List ι,
      l.Nodup ∧ Route R ((l.map C).sum) u v := by
  classical
  obtain ⟨walk⟩ := hreach
  let p := walk.toPath
  have hnd : p.val.support.Nodup := p.property.support_nodup
  exact ⟨p.val.support, hnd,
    route_of_region_walk R S C hlocal p.val u hu v hv⟩

/-- Closed-face trace routing with arbitrary ambient parent-edge local budgets,
exposing exactly the distinct face labels used by the resulting simple
intersection path. This is the path-sensitive form of
`route_of_preconnected_face_cover_with_parent_routes`. -/
theorem route_of_preconnected_face_cover_with_parent_routes_used_labels
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
    ∃ l : List ι,
      l.Nodup ∧ Route (Adj P) ((l.map B).sum) u v := by
  classical
  obtain ⟨i, hui⟩ := hcover u huK
  obtain ⟨j, hvj⟩ := hcover v hvK
  obtain ⟨p⟩ :=
    region_walk_of_preconnected_closed_cover F hclosed K hK hcover huK hvK i j hui hvj
  have hreach := face_walk_to_parent_vertex_walk P F hP hF hclosed p
  obtain ⟨l, hnd, hr⟩ :=
    route_of_connected_regions_with_used_labels
      (Adj P) (fun k => extremePoints ℝ P ∩ F k) B hlocal
      hreach u v ⟨hu, hui⟩ ⟨hv, hvj⟩
  exact ⟨l, hnd, hr⟩

#print axioms route_of_connected_regions_with_used_labels
#print axioms route_of_preconnected_face_cover_with_parent_routes_used_labels

end HirschRegionRoute
