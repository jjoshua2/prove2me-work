import Solutions.PolynomialDeferredClipping

/-!
# Simultaneous clipping with deferred cut-pair costs

This is the quantifier-order version of the shortest-pair clipping theorem.
The radial repair geometry first chooses one metric-shortest/chordless mixed
region path and its concrete parent-vertex portal pairs.  Only afterward does a
caller choose cut-pair costs and supply routes for the projected cut legs that
actually occur.  Old-edge and endpoint-singleton legs are discharged
internally. The full certificate additionally retains region geometry for the
carrier-excess assembly; this module preserves the original projected API.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRegionRoute

set_option autoImplicit false
set_option maxHeartbeats 9000000

noncomputable section
namespace HirschRadial

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- Simultaneous clipping on one supplied outer route with shortest/chordless
mixed geometry fixed before any final-cut local route obligations are given.

The returned callback asks for routes only on `clipRepairCutLegs legs`; every
old-edge leg costs one and every endpoint singleton costs zero internally. -/
theorem route_clip_of_lifted_endpoints_with_shortest_deferred_cut_legs
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQc : IsCompact Q) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (D : ℕ)
    (o : EuclideanSpace ℝ (Fin d)) (ho : o ∈ Q)
    (hstrict : ∀ i, ⟪a i, o⟫ < b i)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (clipSet Q a b))
    (hv : v ∈ extremePoints ℝ (clipSet Q a b))
    (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ Q) (hy : y ∈ extremePoints ℝ Q)
    (hux : u = x ∨ ∃ i, ⟪a i, u⟫ = b i ∧ b i ≤ ⟪a i, x⟫)
    (hvy : v = y ∨ ∃ i, ⟪a i, v⟫ = b i ∧ b i ≤ ⟪a i, y⟫)
    (hwalk : Route (Adj Q) D x y) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
      ∃ i j : Sum ι (Sum (Fin D) (Fin 2)),
      ∃ p :
          (intersectionGraph (fun k =>
            extremePoints ℝ (clipSet Q a b) ∩
              clipRepairPathRegion (D := D) (clipSet Q a b) a b w u v k)).Walk i j,
        p.length =
          (intersectionGraph (fun k =>
            extremePoints ℝ (clipSet Q a b) ∩
              clipRepairPathRegion (D := D) (clipSet Q a b) a b w u v k)).dist i j ∧
        p.IsPath ∧ WalkChordless p ∧
        ∃ legs : List
            (RegionLeg (Sum ι (Sum (Fin D) (Fin 2)))
              (EuclideanSpace ℝ (Fin d))),
          legs.map RegionLeg.label = p.support ∧
          (legs.map RegionLeg.label).Nodup ∧
          (∀ cut ∈ clipRepairCutLegs legs,
            cut.entry ∈ extremePoints ℝ (clipSet Q a b) ∧
            ⟪a cut.label, cut.entry⟫ = b cut.label ∧
            cut.exit ∈ extremePoints ℝ (clipSet Q a b) ∧
            ⟪a cut.label, cut.exit⟫ = b cut.label) ∧
          ∀ (B : ι → EuclideanSpace ℝ (Fin d) →
              EuclideanSpace ℝ (Fin d) → ℕ),
            (∀ cut ∈ clipRepairCutLegs legs,
              Route (Adj (clipSet Q a b))
                (B cut.label cut.entry cut.exit) cut.entry cut.exit) →
            Route (Adj (clipSet Q a b))
              (D + ((clipRepairCutLegs legs).map fun leg =>
                B leg.label leg.entry leg.exit).sum) u v := by
  classical
  obtain ⟨c⟩ := deferred_clip_certificate_of_lifted_endpoints
    Q hQc hQ a b D o ho hstrict u v hu hv x y hx hy hux hvy hwalk
  refine ⟨c.trace, c.startLabel, c.endLabel, c.path, c.shortest, c.isPath,
    c.chordless, c.legs, c.labels, c.nodup, ?_, c.assemble⟩
  intro cut hcut
  obtain ⟨mixed, hmixed, hmap⟩ := List.mem_filterMap.mp hcut
  rcases mixed with ⟨label, entry, exit⟩
  rcases label with i | rest
  · simp only at hmap
    injection hmap with heq
    subst cut
    have hf := c.fits (RegionLeg.mk (Sum.inl i) entry exit) hmixed
    exact ⟨hf.1.1, hf.1.2.2, hf.2.1.1, hf.2.1.2.2⟩
  · simp at hmap

/-- Endpoint-lifted wrapper from an outer diameter bound, still deferring all
final-cut pair costs until after the shortest mixed repair path and concrete
cut portal pairs have been selected. -/
theorem route_clip_with_shortest_deferred_cut_legs
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQc : IsCompact Q) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (D : ℕ) (hD : DiamLE Q D)
    (o : EuclideanSpace ℝ (Fin d)) (ho : o ∈ Q)
    (hstrict : ∀ i, ⟪a i, o⟫ < b i)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (clipSet Q a b))
    (hv : v ∈ extremePoints ℝ (clipSet Q a b)) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
      ∃ i j : Sum ι (Sum (Fin D) (Fin 2)),
      ∃ p :
          (intersectionGraph (fun k =>
            extremePoints ℝ (clipSet Q a b) ∩
              clipRepairPathRegion (D := D) (clipSet Q a b) a b w u v k)).Walk i j,
        p.length =
          (intersectionGraph (fun k =>
            extremePoints ℝ (clipSet Q a b) ∩
              clipRepairPathRegion (D := D) (clipSet Q a b) a b w u v k)).dist i j ∧
        p.IsPath ∧ WalkChordless p ∧
        ∃ legs : List
            (RegionLeg (Sum ι (Sum (Fin D) (Fin 2)))
              (EuclideanSpace ℝ (Fin d))),
          legs.map RegionLeg.label = p.support ∧
          (legs.map RegionLeg.label).Nodup ∧
          (∀ cut ∈ clipRepairCutLegs legs,
            cut.entry ∈ extremePoints ℝ (clipSet Q a b) ∧
            ⟪a cut.label, cut.entry⟫ = b cut.label ∧
            cut.exit ∈ extremePoints ℝ (clipSet Q a b) ∧
            ⟪a cut.label, cut.exit⟫ = b cut.label) ∧
          ∀ (B : ι → EuclideanSpace ℝ (Fin d) →
              EuclideanSpace ℝ (Fin d) → ℕ),
            (∀ cut ∈ clipRepairCutLegs legs,
              Route (Adj (clipSet Q a b))
                (B cut.label cut.entry cut.exit) cut.entry cut.exit) →
            Route (Adj (clipSet Q a b))
              (D + ((clipRepairCutLegs legs).map fun leg =>
                B leg.label leg.entry leg.exit).sum) u v := by
  obtain ⟨x, hx, hux⟩ :=
    HirschClipLift.endpoint_lift_to_outer_vertex Q hQc hQ a b u hu
  obtain ⟨y, hy, hvy⟩ :=
    HirschClipLift.endpoint_lift_to_outer_vertex Q hQc hQ a b v hv
  exact route_clip_of_lifted_endpoints_with_shortest_deferred_cut_legs
    Q hQc hQ a b D o ho hstrict u v hu hv x y hx hy hux hvy (hD x hx y hy)

#print axioms route_clip_of_lifted_endpoints_with_shortest_deferred_cut_legs
#print axioms route_clip_with_shortest_deferred_cut_legs

end HirschRadial
