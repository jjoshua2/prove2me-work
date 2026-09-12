# Simultaneous clipping used-region support verification

Date: 2026-09-12.

Frozen theorem head: `d20dda84130afbb6a5ad8d89ec86e214a2f03053`.

Hosted verification:
- run `34690672153`
- job `103545246527`
- artifact `10297068128`
- artifact digest `sha256:2b64fe2890c49bf3473843567942236b787a687ac1222f9c119c5d7810217be8`
- Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The ready-for-review one-shot gate built `Solutions.PolynomialSimultaneousClipUsedRegions` and transitive-axiom-audited all seven printed public declarations. Every report contains only the repository-allowed standard logical axioms (`propext`, `Classical.choice`, `Quot.sound`); the arithmetic decomposition itself uses only `propext` and `Quot.sound`.

Verified declarations:
- `HirschRadial.clipRepairRegionCost_sum_eq_cut_add_old_length`
- `HirschRadial.route_clip_of_lifted_endpoints_with_parent_routes_used_regions`
- `HirschRadial.route_clip_of_lifted_endpoints_with_parent_routes_used_cut_faces`
- `HirschRadial.route_clip_with_parent_routes_used_regions`
- `HirschRadial.route_clip_with_parent_routes_used_cut_faces`
- `HirschRadial.route_clip_from_root_with_parent_routes_used_regions`
- `HirschRadial.route_clip_from_root_with_parent_routes_used_cut_faces`

Formal contribution: the simultaneous radial repair now exposes the simple `Nodup` mixed region support actually used by a route. Projecting that support to final cut faces stays `Nodup`; projecting to old outer-edge pieces also stays `Nodup` and uses at most `D` labels because those labels lie in `Fin D`. The exact mixed cost decomposes into the used-cut budget sum plus the number of used old-edge labels. Hence the clean theorem pads only to

`D + sum_{used cut faces} B_i`,

rather than `D + sum_{all cut faces} B_i`.

Endpoint-lift singleton regions have zero cost. The theorem does not bound the used face budgets themselves and therefore does not establish a fixed-degree Polynomial Hirsch recurrence.

No Prove2Me credentials or mutation were used. The one-shot verifier is removed before integration.
