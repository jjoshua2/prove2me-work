# Used-region portal-path verification

Date: 2026-09-12.

Frozen theorem head: `da004e85bc8779799f4e18192f174812756c9f70`.

Hosted verification:
- run `34691141709`
- job `103546479666`
- artifact `10296769324`
- artifact digest `sha256:1ef5052d709e5ca2964bc75057784fdb1e4dcff211f7303947de71a12f4ebecc`
- Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The one-shot hosted gate built `Solutions.PolynomialUsedRegionPortalPath` and transitive-axiom-audited:
- `HirschRegionRoute.route_of_connected_regions_with_used_path`
- `HirschRegionRoute.route_of_preconnected_face_cover_with_parent_routes_used_path`
- `HirschRegionRoute.parent_vertex_portal_of_used_path_edge`

All three reports contain only the standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`.

Formal contribution: support-sensitive region routing now retains the actual simple intersection-graph path, not only its `Nodup` support list.  In the closed extreme-face specialization the graph vertices are `extremePoints ℝ P ∩ F i`, so every graph edge carries an explicit shared **parent extreme vertex** lying in the two consecutive faces.  This preserves the portal geometry needed to replace uniform whole-face diameter budgets by pair-specific local route budgets in later work.

No smaller portal-pair cost is claimed here.  The weighted recursive face-cost obstruction remains open.  No Prove2Me credentials or mutation were used.  The one-shot verifier is removed before integration.
