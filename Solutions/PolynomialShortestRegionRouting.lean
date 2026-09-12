import Mathlib
import Solutions.PolynomialPairSpecificRegionLegs

/-!
# Shortest, chordless region routing before pair-specific costs

The pair-specific region-leg interface must not first choose an arbitrary simple
path and then shortcut it after local costs are attached: a shortcut can change
the actual portal pair and hence its cost.  Instead this module chooses a
metric-shortest walk in the region-intersection graph *before* making any local
routing calls.

A shortest walk is chordless in the precise index sense needed downstream: two
vertices separated by at least one intermediate path vertex cannot be adjacent.
The proof explicitly replaces the skipped subwalk by the alleged chord and
contradicts graph-distance minimality.

The final theorem then runs the existing pair-specific leg construction on this
fixed shortest path.  Thus its concrete `(label, entry, exit)` calls are attached
only after the chordless support has been chosen.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section

namespace HirschRegionRoute

/-- A walk has no chord joining vertices which have an intermediate vertex
between them along the walk.  Consecutive vertices are intentionally allowed to
be adjacent: those are exactly the walk edges. -/
def WalkChordless {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : Prop :=
  ∀ r s : ℕ, r + 1 < s → s ≤ p.length →
    ¬ G.Adj (p.getVert r) (p.getVert s)

/-- A walk whose length realizes graph distance is chordless.

If `p[r]` and `p[s]` with `r+1<s` were adjacent, concatenate the first `r`
edges, that one chord, and the suffix beginning at `s`.  The resulting walk has
length `r+1+(L-s) < L`, contradicting `L = dist`. -/
theorem shortest_walk_chordless
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.length = G.dist u v) :
    WalkChordless p := by
  intro r s hrs hs hadj
  have hr : r ≤ p.length := by omega
  let q : G.Walk u v :=
    ((p.take r).concat hadj).append (p.drop s)
  have hdist : G.dist u v ≤ q.length := SimpleGraph.dist_le q
  have hqlen : q.length = r + 1 + (p.length - s) := by
    simp [q, hr]
  rw [← hp] at hdist
  rw [hqlen] at hdist
  omega

/-- Reachability supplies a shortest walk which is simultaneously a path and
chordless.  The path property follows from Mathlib's metric minimality theorem;
chordlessness is the stronger nonconsecutive-adjacency statement above. -/
theorem exists_shortest_chordless_walk
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (hreach : G.Reachable u v) :
    ∃ p : G.Walk u v,
      p.length = G.dist u v ∧ p.IsPath ∧ WalkChordless p := by
  obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
  exact ⟨p, hp, p.isPath_of_length_eq_dist hp, shortest_walk_chordless p hp⟩

/-- Pair-specific connected-region routing on a shortest/chordless region path.

The important ordering is existentially visible in the conclusion: the shortest
path is chosen first; only then are the actual local `RegionLeg`s and their
pair-specific costs constructed.  Leg labels equal the path support and are
therefore duplicate-free. -/
theorem route_of_connected_regions_with_shortest_pair_specific_legs
    {V ι : Type*} [Fintype ι]
    (R : V → V → Prop) (S : ι → Set V)
    (C : ι → V → V → ℕ)
    (hlocal : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, Route R (C i u v) u v)
    {i j : ι} (hreach : Nonempty ((intersectionGraph S).Walk i j))
    (u v : V) (hu : u ∈ S i) (hv : v ∈ S j) :
    ∃ p : (intersectionGraph S).Walk i j,
      p.length = (intersectionGraph S).dist i j ∧
      p.IsPath ∧ WalkChordless p ∧
      ∃ legs : List (RegionLeg ι V),
        legs.map RegionLeg.label = p.support ∧
        (legs.map RegionLeg.label).Nodup ∧
        (∀ leg ∈ legs, RegionLegFits S u v leg) ∧
        Route R
          ((legs.map fun leg => C leg.label leg.entry leg.exit).sum) u v := by
  classical
  have hr : (intersectionGraph S).Reachable i j := hreach
  obtain ⟨p, hpdist, hpath, hchord⟩ := exists_shortest_chordless_walk hr
  obtain ⟨legs, hlabels, hfits, hroute⟩ :=
    route_of_region_walk_with_pair_specific_legs
      R S C hlocal p u hu v hv
  have hnd : (legs.map RegionLeg.label).Nodup := by
    rw [hlabels]
    exact hpath.support_nodup
  exact ⟨p, hpdist, hpath, hchord, legs, hlabels, hnd, hfits, hroute⟩

/-- Closed extreme-face specialization retaining a shortest/chordless path in
the parent-vertex intersection graph and the actual pair-specific portal legs.
Every leg endpoint is a parent extreme vertex in its labelled face. -/
theorem route_of_preconnected_face_cover_with_shortest_pair_specific_legs
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
        p.length =
          (intersectionGraph (fun k => extremePoints ℝ P ∩ F k)).dist i j ∧
        p.IsPath ∧ WalkChordless p ∧
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
  obtain ⟨p, hpdist, hp, hchord, legs, hlabels, hnd, hfits, hr⟩ :=
    route_of_connected_regions_with_shortest_pair_specific_legs
      (Adj P) (fun k => extremePoints ℝ P ∩ F k) C hlocal
      hreach u v ⟨hu, hui⟩ ⟨hv, hvj⟩
  exact ⟨i, j, ⟨hu, hui⟩, ⟨hv, hvj⟩,
    p, hpdist, hp, hchord, legs, hlabels, hnd, hfits, hr⟩

#print axioms shortest_walk_chordless
#print axioms exists_shortest_chordless_walk
#print axioms route_of_connected_regions_with_shortest_pair_specific_legs
#print axioms route_of_preconnected_face_cover_with_shortest_pair_specific_legs

end HirschRegionRoute
