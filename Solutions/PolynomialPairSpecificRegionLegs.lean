import Mathlib
import Solutions.PolynomialUsedRegionPortalPath

/-!
# Pair-specific region legs

The used-region path records which faces occur and which consecutive faces have
a shared parent-vertex portal.  To attack the remaining weighted face-budget
obstruction we also need the *actual pair of vertices routed inside each face*.

This module exposes those local calls as `RegionLeg`s.  A leg remembers its
region label, entry point and exit point.  Every leg endpoint lies in its own
region, and every endpoint other than the two global route endpoints is also a
member of another region: it is an actual intersection portal.

Local budgets may now depend on `(label, entry, exit)` rather than only on the
label.  The global route budget is exactly the sum of those pair-specific local
budgets.  For parent extreme-face regions this means every leg is between two
parent vertices in the face, with non-global endpoints certified as shared
parent-vertex portals.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section
namespace HirschRegionRoute

/-- One actual local routing call made while traversing a region path. -/
structure RegionLeg (ι V : Type*) where
  label : ι
  entry : V
  exit : V

/-- A point is a portal for region `i` when it also lies in a distinct region. -/
def IsRegionPortal {V ι : Type*} (S : ι → Set V) (i : ι) (x : V) : Prop :=
  ∃ j : ι, j ≠ i ∧ x ∈ S j

/-- A local leg is geometrically compatible with the global route endpoints:
both endpoints lie in its own region, and each is either the corresponding
global endpoint or a genuine portal to another region. -/
def RegionLegFits {V ι : Type*} (S : ι → Set V) (u v : V)
    (leg : RegionLeg ι V) : Prop :=
  leg.entry ∈ S leg.label ∧
  leg.exit ∈ S leg.label ∧
  (leg.entry = u ∨ IsRegionPortal S leg.label leg.entry) ∧
  (leg.exit = v ∨ IsRegionPortal S leg.label leg.exit)

/-- Traverse a fixed region walk with a genuinely pair-specific local cost.
The returned leg labels are exactly the walk support, and the global route cost
is exactly the sum of the local costs on the returned entry/exit pairs. -/
theorem route_of_region_walk_with_pair_specific_legs
    {V ι : Type*}
    (R : V → V → Prop) (S : ι → Set V)
    (C : ι → V → V → ℕ)
    (hlocal : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, Route R (C i u v) u v)
    {i j : ι} (p : (intersectionGraph S).Walk i j) :
    ∀ u ∈ S i, ∀ v ∈ S j,
      ∃ legs : List (RegionLeg ι V),
        legs.map RegionLeg.label = p.support ∧
        (∀ leg ∈ legs, RegionLegFits S u v leg) ∧
        Route R
          ((legs.map fun leg => C leg.label leg.entry leg.exit).sum) u v := by
  classical
  induction p with
  | @nil i =>
      intro u hu v hv
      let leg : RegionLeg ι V := ⟨i, u, v⟩
      refine ⟨[leg], ?_, ?_, ?_⟩
      · simp [leg]
      · intro q hq
        simp only [List.mem_singleton] at hq
        subst q
        exact ⟨hu, hv, Or.inl rfl, Or.inl rfl⟩
      · simpa [leg] using hlocal i u hu v hv
  | @cons i k j hik p ih =>
      intro u hu v hv
      obtain ⟨z, hzi, hzk⟩ := hik.2
      obtain ⟨legs, hlabels, hfits, htail⟩ := ih z hzk v hv
      let first : RegionLeg ι V := ⟨i, u, z⟩
      have hfirst : Route R (C i u z) u z := hlocal i u hu z hzi
      obtain ⟨a, ha0, haC, has⟩ := hfirst
      obtain ⟨b, hb0, hbC, hbs⟩ := htail
      obtain ⟨q, hq0, hqC, hqs⟩ :=
        HirschProduct.append_walk R a b ha0 haC hb0 hbC has hbs
      refine ⟨first :: legs, ?_, ?_, ?_⟩
      · simp [first, hlabels]
      · intro leg hleg
        rcases List.mem_cons.mp hleg with hfirstLeg | htailLeg
        · subst leg
          refine ⟨hu, hzi, Or.inl rfl, Or.inr ?_⟩
          exact ⟨k, Ne.symm hik.1, hzk⟩
        · obtain ⟨hentryMem, hexitMem, hentry, hexit⟩ := hfits leg htailLeg
          refine ⟨hentryMem, hexitMem, ?_, hexit⟩
          rcases hentry with hentryEq | hentryPortal
          · right
            rw [hentryEq]
            by_cases hli : leg.label = i
            · refine ⟨k, ?_, hzk⟩
              simpa [hli] using (Ne.symm hik.1)
            · exact ⟨i, fun h => hli h.symm, hzi⟩
          · exact Or.inr hentryPortal
      · simpa [first, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (show Route R
            (C i u z + (legs.map fun leg => C leg.label leg.entry leg.exit).sum) u v from
              ⟨q, hq0, hqC, hqs⟩)

/-- Connected routing with an actual simple region path and the pair-specific
legs routed along that path.  In particular the leg-label list is duplicate
free because it equals the support of a path. -/
theorem route_of_connected_regions_with_pair_specific_legs
    {V ι : Type*} [Fintype ι]
    (R : V → V → Prop) (S : ι → Set V)
    (C : ι → V → V → ℕ)
    (hlocal : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, Route R (C i u v) u v)
    {i j : ι} (hreach : Nonempty ((intersectionGraph S).Walk i j))
    (u v : V) (hu : u ∈ S i) (hv : v ∈ S j) :
    ∃ p : (intersectionGraph S).Walk i j,
      p.IsPath ∧
      ∃ legs : List (RegionLeg ι V),
        legs.map RegionLeg.label = p.support ∧
        (legs.map RegionLeg.label).Nodup ∧
        (∀ leg ∈ legs, RegionLegFits S u v leg) ∧
        Route R
          ((legs.map fun leg => C leg.label leg.entry leg.exit).sum) u v := by
  classical
  obtain ⟨walk⟩ := hreach
  let p := walk.toPath
  obtain ⟨legs, hlabels, hfits, hr⟩ :=
    route_of_region_walk_with_pair_specific_legs
      R S C hlocal p.val u hu v hv
  refine ⟨p.val, p.property, legs, hlabels, ?_, hfits, hr⟩
  rw [hlabels]
  exact p.property.support_nodup

/-- Closed extreme-face specialization.  Every returned local leg is between
parent extreme vertices in one face; every non-global leg endpoint is a shared
parent-vertex portal to another face.  The supplied local cost may depend on
that actual portal pair. -/
theorem route_of_preconnected_face_cover_with_pair_specific_legs
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (C : ι → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℕ)
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i))
    (hlocal : ∀ i,
      ∀ u ∈ extremePoints ℝ P ∩ F i,
      ∀ v ∈ extremePoints ℝ P ∩ F i,
        Route (Adj P) (C i u v) u v)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsPreconnected K)
    (hcover : ∀ x ∈ K, ∃ i, x ∈ F i)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ P) (hv : v ∈ extremePoints ℝ P)
    (huK : u ∈ K) (hvK : v ∈ K) :
    ∃ i j : ι,
      u ∈ extremePoints ℝ P ∩ F i ∧
      v ∈ extremePoints ℝ P ∩ F j ∧
      ∃ p : (intersectionGraph (fun k => extremePoints ℝ P ∩ F k)).Walk i j,
        p.IsPath ∧
        ∃ legs : List (RegionLeg ι (EuclideanSpace ℝ (Fin d))),
          legs.map RegionLeg.label = p.support ∧
          (legs.map RegionLeg.label).Nodup ∧
          (∀ leg ∈ legs,
            RegionLegFits (fun k => extremePoints ℝ P ∩ F k) u v leg) ∧
          Route (Adj P)
            ((legs.map fun leg => C leg.label leg.entry leg.exit).sum) u v := by
  classical
  obtain ⟨i, hui⟩ := hcover u huK
  obtain ⟨j, hvj⟩ := hcover v hvK
  obtain ⟨faceWalk⟩ :=
    region_walk_of_preconnected_closed_cover
      F hclosed K hK hcover huK hvK i j hui hvj
  have hreach := face_walk_to_parent_vertex_walk P F hP hF hclosed faceWalk
  obtain ⟨p, hp, legs, hlabels, hnd, hfits, hr⟩ :=
    route_of_connected_regions_with_pair_specific_legs
      (Adj P) (fun k => extremePoints ℝ P ∩ F k) C hlocal
      hreach u v ⟨hu, hui⟩ ⟨hv, hvj⟩
  exact ⟨i, j, ⟨hu, hui⟩, ⟨hv, hvj⟩,
    p, hp, legs, hlabels, hnd, hfits, hr⟩

#print axioms route_of_region_walk_with_pair_specific_legs
#print axioms route_of_connected_regions_with_pair_specific_legs
#print axioms route_of_preconnected_face_cover_with_pair_specific_legs

end HirschRegionRoute
