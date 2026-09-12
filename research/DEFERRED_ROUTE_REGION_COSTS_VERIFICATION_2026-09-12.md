# Deferred padded region-cost routing verification

Date: 2026-09-12.

Frozen theorem head: `be8b34a4e37df36e8f2702938d83a9210f5e6338`.

Hosted verification:
- run `34705245819`
- job `103584019037`
- artifact `10301029688`
- artifact digest `sha256:ac0c33bd6eb032cbca6ac41f05b9603d650f1c3bc5c66994de1bdaac0ec2c234`
- Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The first and only focused gate compiled `Solutions.PolynomialDeferredRouteRegionCosts` and transitive-axiom-audited both public declarations. The reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

Verified declarations:
- `HirschRegionRoute.route_of_connected_regions_with_shortest_deferred_route_legs`
- `HirschRegionRoute.route_of_preconnected_face_cover_with_shortest_deferred_parent_legs`

Formal contribution: the shortest/chordless region path and concrete entry/exit portal pairs are selected before any padded local `Route` cost assignment or local route proof is supplied. One fixed duplicate-free leg list then works for every later cost function; only those selected legs need local routes. The closed extreme-face specialization fixes actual parent-vertex portal pairs before any parent-edge routing obligations.

This is the stay-aware routing counterpart of the accepted public theorem `Hirsch.shortest_region_path_with_deferred_pair_costs` and is the quantifier-order adapter needed to thread deferred costs through simultaneous clipping. It does not itself supply local cut-leg routes or prove a diameter bound.

No Prove2Me credentials or mutation were used. The one-shot verifier is removed before integration.
