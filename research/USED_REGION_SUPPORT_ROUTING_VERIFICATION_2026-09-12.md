# Used-region support routing verification

Date: 2026-09-12.

Frozen theorem head: `d55f49f6dbde636f2eb9f4d80c72f84a4677c2b3`.

Hosted verification:
- run `34676515733`
- job `103507229738`
- artifact `10292881805`
- artifact digest `sha256:f4844cf502c44eb2ecf605e9643bf57ce8e5e0c4473363d2d1bc3d0728bf08d9`
- Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The focused ready-for-review gate compiled `Solutions.PolynomialUsedRegionRouting` and axiom-audited both public declarations. Their transitive axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

Verified declarations:
- `HirschRegionRoute.route_of_connected_regions_with_used_labels`
- `HirschRegionRoute.route_of_preconnected_face_cover_with_parent_routes_used_labels`

Formal contribution: instead of padding a connected-region repair to the sum over every available label, the theorem exposes the actual simple region path obtained after cycle erasure. Its label list is `Nodup`, and the route length is exactly the sum of the local budgets on those used labels. The closed-face specialization does the same for ambient parent-edge routing through a connected trace.

This is an accounting interface, not a new diameter bound by itself. In the target-cone reinsertion line it enables future weighted/rank amortization on the face labels actually charged, rather than automatically charging every target-slack row.

No Prove2Me credentials or mutation were used. The one-shot verifier is removed before integration.
