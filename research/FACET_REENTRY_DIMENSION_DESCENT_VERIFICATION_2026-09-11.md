# Facet reentry dimension descent — hosted verification receipt

Date: 2026-09-11

Frozen proof source commit `8c5529b71185f4f72b5cabbefa48c7ccde8acdef` passed the focused hosted gate under Lean 4.30.0 and Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

- PR: #149
- Actions run: `34654862794`
- job: `103444935535`
- conclusion: **success**
- artifact: `10284704315`, `facet-reentry-dimension-descent-verification`
- artifact digest: `sha256:abd5684135cff6972c4b41dc86a2917941b9cce9041d6507634c5c43cfeba465`

`Solutions/PolynomialFacetReentryDimensionDescent.lean` built successfully. The gate axiom-audited:

- `HirschFaceSplice.splice_reentry_through_parent_route`
- `HirschFaceSplice.hpoly_facet_parent_route_of_lower_dimension_bound`
- `HirschFaceSplice.splice_reentry_through_hpoly_facet_of_lower_dimension_bound`

All three complete axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The checker reported:

`Axiom audit passed: 3 required declarations; 3 reports checked; only standard logical axioms.`

## Result

Repeated exits and reentries between the first and last selected visits to one nonzero-row facet of a bounded `(k+1)`-row, `d`-dimensional H-polyhedron can be replaced by one ambient parent-edge route supplied by a `k`-row, `(d-1)`-dimensional recursive diameter bound. Thus the whole reentry interval pays one lower-dimensional budget `B`, not one charge per reentry.

This is an ambient parent-edge statement; the replacement path need not remain intrinsically inside the facet. Row excess is preserved by the `(k+1,d) -> (k,d-1)` recursion.

No Prove2Me publication occurred in this verification run. This theorem is a cost-side ingredient and does not itself solve the Polynomial Hirsch refinement target.
