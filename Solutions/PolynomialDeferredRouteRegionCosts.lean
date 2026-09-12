import Mathlib
import Solutions.PolynomialShortestRegionRouting

/-!
# Deferred local costs for padded Route assembly

The public Prove2Me theorem `Hirsch.shortest_region_path_with_deferred_pair_costs`
uses `SimpleGraph.Walk`.  The clipping stack uses the repository's padded `Route`
interface, where stationary steps are allowed.  This module gives the exact
stay-aware analogue: region geometry, shortest/chordless support and actual
portal pairs are fixed before any local route-cost obligation is supplied.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section
namespace HirschRegionRoute

private theorem route_of_region_walk_with_deferred_route_legs
    {V ι : Type*}
    (R : V → V → Prop) (S : ι → Set V)
    {i j : ι} (p : (intersectionGraph S).Walk i j) :
    ∀ u ∈ S i, ∀ v ∈ S j,
      ∃ legs : List (RegionLeg ι V),
        legs.map RegionLeg.label = p.support ∧
        (∀ leg ∈ legs, RegionLegFits S u v leg) ∧
        ∀ (C : ι → V → V → ℕ),
          (∀ leg ∈ legs,
            Route R (C leg.label leg.entry leg.exit) leg.entry leg.exit) →
          Route R
            ((legs.map fun leg => C leg.label leg.entry leg.exit).sum) u v := by
  classical
  induction p with
  | @nil i =>
      intro u hu v hv
      let leg : RegionLeg ι V := ⟨i, u, v⟩
      refine ⟨[leg], by simp [leg], ?_, ?_⟩
      · intro q hq
        simp only [List.mem_singleton] at hq
        subst q
        exact ⟨hu, hv, Or.inl rfl, Or.inl rfl⟩
      · intro C hlocal
        simpa [leg] using hlocal leg (by simp [leg])
  | @cons i k j hik p ih =>
      intro u hu v hv
      obtain ⟨z, hzi, hzk⟩ := hik.2
      obtain ⟨legs, hlabels, hfits, htail⟩ := ih z hzk v hv
      let first : RegionLeg ι V := ⟨i, u, z⟩
      refine ⟨first :: legs, by simp [first, hlabels], ?_, ?_⟩
      · intro leg hleg
        rcases List.mem_cons.mp hleg with hfirst | hrest
        · subst leg
          refine ⟨hu, hzi, Or.inl rfl, Or.inr ?_⟩
          exact ⟨k, Ne.symm hik.1, hzk⟩
        · obtain ⟨hentryMem, hexitMem, hentry, hexit⟩ := hfits leg hrest
          refine ⟨hentryMem, hexitMem, ?_, hexit⟩
          rcases hentry with hentryEq | hentryPortal
          · right
            rw [hentryEq]
            by_cases hli : leg.label = i
            · refine ⟨k, ?_, hzk⟩
              simpa [hli] using (Ne.symm hik.1)
            · exact ⟨i, fun h => hli h.symm, hzi⟩
          · exact Or.inr hentryPortal
      · intro C hlocal
        have hfirstRoute : Route R (C i u z) u z :=
          hlocal first (by simp [first])
        have htailRoute :
            Route R
              ((legs.map fun leg => C leg.label leg.entry leg.exit).sum) z v :=
          htail C (fun leg hleg => hlocal leg (List.mem_cons_of_mem _ hleg))
        obtain ⟨a, ha0, haC, has⟩ := hfirstRoute
        obtain ⟨b, hb0, hbC, hbs⟩ := htailRoute
        obtain ⟨q, hq0, hqC, hqs⟩ :=
          HirschProduct.append_walk R a b ha0 haC hb0 hbC has hbs
        simpa [first, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (show Route R
            (C i u z + (legs.map fun leg =>
              C leg.label leg.entry leg.exit).sum) u v from
              ⟨q, hq0, hqC, hqs⟩)

/-- Choose a shortest/chordless region path and its actual portal pairs BEFORE
asking for padded local routes.  The same concrete leg list then works for every
subsequent cost assignment `C`; only those selected legs need route proofs. -/
theorem route_of_connected_regions_with_shortest_deferred_route_legs
    {V ι : Type*} [Fintype ι]
    (R : V → V → Prop) (S : ι → Set V)
    {i j : ι} (hreach : Nonempty ((intersectionGraph S).Walk i j))
    (u v : V) (hu : u ∈ S i) (hv : v ∈ S j) :
    ∃ p : (intersectionGraph S).Walk i j,
      p.length = (intersectionGraph S).dist i j ∧
      p.IsPath ∧ WalkChordless p ∧
      ∃ legs : List (RegionLeg ι V),
        legs.map RegionLeg.label = p.support ∧
        (legs.map RegionLeg.label).Nodup ∧
        (∀ leg ∈ legs, RegionLegFits S u v leg) ∧
        ∀ (C : ι → V → V → ℕ),
          (∀ leg ∈ legs,
            Route R (C leg.label leg.entry leg.exit) leg.entry leg.exit) →
          Route R
            ((legs.map fun leg => C leg.label leg.entry leg.exit).sum) u v := by
  classical
  have hr : (intersectionGraph S).Reachable i j := hreach
  obtain ⟨p, hpdist, hpath, hchord⟩ := exists_shortest_chordless_walk hr
  obtain ⟨legs, hlabels, hfits, hroute⟩ :=
    route_of_region_walk_with_deferred_route_legs R S p u hu v hv
  have hnd : (legs.map RegionLeg.label).Nodup := by
    rw [hlabels]
    exact hpath.support_nodup
  exact ⟨p, hpdist, hpath, hchord, legs, hlabels, hnd, hfits, hroute⟩

/-- Closed extreme-face specialization.  Parent geometry and actual
parent-vertex portal pairs are selected before any local parent-edge route
obligation is introduced. -/
theorem route_of_preconnected_face_cover_with_shortest_deferred_parent_legs
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i))
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsPreconnected K)
    (hcover : ∀ x ∈ K, ∃ i, x ∈ F i)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ P) (hv : v ∈ extremePoints ℝ P)
    (huK : u ∈ K) (hvK : v ∈ K) :
    ∃ i j : ι,
      u ∈ extremePoints ℝ P ∩ F i ∧
      v ∈ extremePoints ℝ P ∩ F j ∧
      ∃ p : (intersectionGraph (fun k => extremePoints ℝ P ∩ F k)).Walk i j,
        p.length =
          (intersectionGraph (fun k => extremePoints ℝ P ∩ F k)).dist i j ∧
        p.IsPath ∧ WalkChordless p ∧
        ∃ legs : List (RegionLeg ι (EuclideanSpace ℝ (Fin d))),
          legs.map RegionLeg.label = p.support ∧
          (legs.map RegionLeg.label).Nodup ∧
          (∀ leg ∈ legs,
            RegionLegFits (fun k => extremePoints ℝ P ∩ F k) u v leg) ∧
          ∀ (C : ι → EuclideanSpace ℝ (Fin d) →
              EuclideanSpace ℝ (Fin d) → ℕ),
            (∀ leg ∈ legs,
              Route (Adj P) (C leg.label leg.entry leg.exit)
                leg.entry leg.exit) →
            Route (Adj P)
              ((legs.map fun leg => C leg.label leg.entry leg.exit).sum) u v := by
  classical
  obtain ⟨i, hui⟩ := hcover u huK
  obtain ⟨j, hvj⟩ := hcover v hvK
  obtain ⟨faceWalk⟩ :=
    region_walk_of_preconnected_closed_cover
      F hclosed K hK hcover huK hvK i j hui hvj
  have hreach := face_walk_to_parent_vertex_walk P F hP hF hclosed faceWalk
  obtain ⟨p, hpdist, hpath, hchord, legs, hlabels, hnd, hfits, hroute⟩ :=
    route_of_connected_regions_with_shortest_deferred_route_legs
      (Adj P) (fun k => extremePoints ℝ P ∩ F k)
      hreach u v ⟨hu, hui⟩ ⟨hv, hvj⟩
  exact ⟨i, j, ⟨hu, hui⟩, ⟨hv, hvj⟩,
    p, hpdist, hpath, hchord, legs, hlabels, hnd, hfits, hroute⟩

#print axioms route_of_connected_regions_with_shortest_deferred_route_legs
#print axioms route_of_preconnected_face_cover_with_shortest_deferred_parent_legs

end HirschRegionRoute
