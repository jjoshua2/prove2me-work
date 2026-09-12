# Pair-specific region-leg verification

Date: 2026-09-12.

Frozen theorem head: `7316e387fc04d4d8144f9afe2366ae0d848f725d`.

Hosted verification:
- run `34691376118`
- job `103547111801`
- artifact `10296578826`
- artifact digest `sha256:daaf00e91501cffd265929c722832796e8dfd58ec2eec32036dbc866efa434d9`
- Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The one-shot hosted gate built `Solutions.PolynomialPairSpecificRegionLegs` and transitive-axiom-audited:
- `HirschRegionRoute.route_of_region_walk_with_pair_specific_legs`
- `HirschRegionRoute.route_of_connected_regions_with_pair_specific_legs`
- `HirschRegionRoute.route_of_preconnected_face_cover_with_pair_specific_legs`

All three reports contain only the standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`.

Formal contribution: local region-routing budgets may depend on the actual `(label, entry, exit)` pair.  The returned `RegionLeg` list has labels exactly equal to the simple region-path support, hence duplicate-free.  Every leg endpoint lies in its own region; every non-global endpoint is additionally certified as a portal lying in another region.  The global route budget is exactly the sum of the pair-specific local leg budgets.

In the compact closed-extreme-face specialization, all leg endpoints are parent extreme vertices in their face.  Thus later recursion can assign a resource/cost to the actual parent-vertex portal pair used in each face, rather than paying a whole-face diameter.  No decreasing pair resource is proved here; the global Polynomial Hirsch recurrence remains open.

No Prove2Me credentials or mutation were used.  The one-shot verifier is removed before integration.
