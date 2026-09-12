# Shortest region routing verification

Date: 2026-09-12.

Frozen theorem head: `8345fa2386d5262e7d0f52d804046a9811cb2eac`.

Hosted verification:
- run `34698222281`
- job `103565282890`
- artifact `10298824557`
- artifact digest `sha256:ab635f80c641775144222dd31e8e9d44f9272443ed7c418f9108c6bd81ad3f8e`
- Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The first and only hosted gate built `Solutions.PolynomialShortestRegionRouting`, ran the source file directly through Lean, and axiom-audited:
- `HirschRegionRoute.shortest_walk_chordless`
- `HirschRegionRoute.exists_shortest_chordless_walk`
- `HirschRegionRoute.route_of_connected_regions_with_shortest_pair_specific_legs`
- `HirschRegionRoute.route_of_preconnected_face_cover_with_shortest_pair_specific_legs`

All four reports contain only `propext`, `Classical.choice`, and `Quot.sound`; the strict checker reports: `Axiom audit passed: 4 required declarations; 4 reports checked; only standard logical axioms.`

Formal contribution: reachable region labels may now be joined by a graph-metric shortest region walk before any local pair-specific routing calls are chosen. A distance-realizing walk is proved chordless: if positions `r,s` satisfy `r+1<s`, their vertices cannot be adjacent, because prefix + that chord + suffix would give a shorter walk. The pair-specific `RegionLeg`s are then constructed on this already-fixed shortest path, so later arguments never need to assume shortcutting preserves the actual portal-pair cost.

The compact closed-extreme-face specialization retains the same shortest/chordless path in the parent-vertex intersection graph together with the actual parent-vertex entry/exit pairs used in every local face call.

This is a path-ordering interface, not a diameter theorem. No Prove2Me credentials or mutation were used. The one-shot verifier is removed before integration.
