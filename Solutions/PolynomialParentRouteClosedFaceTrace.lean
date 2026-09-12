import Solutions.PolynomialClosedFaceTrace

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRegionRoute

/-- A preconnected trace covered by finitely many closed parent faces can be
routed using arbitrary ambient parent-edge budgets on those faces.

Unlike `route_of_preconnected_face_cover`, the local hypothesis need not be an
intrinsic `DiamLE` theorem for each face.  It is enough to route parent vertices
that lie on the face by parent edges.  This is the form supplied by facet
reduction/dimension descent. -/
theorem route_of_preconnected_face_cover_with_parent_routes
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
    Route (Adj P) (∑ i, B i) u v := by
  obtain ⟨i, hui⟩ := hcover u huK
  obtain ⟨j, hvj⟩ := hcover v hvK
  obtain ⟨p⟩ := region_walk_of_preconnected_closed_cover
    F hclosed K hK hcover huK hvK i j hui hvj
  exact route_of_connected_regions
    (Adj P) (fun k => extremePoints ℝ P ∩ F k) B hlocal
    (face_walk_to_parent_vertex_walk P F hP hF hclosed p)
    u v ⟨hu, hui⟩ ⟨hv, hvj⟩

#print axioms route_of_preconnected_face_cover_with_parent_routes

end HirschRegionRoute
