# Low excess by section descent — 2026-09-11

## Status

Complete ordinary induction argument below; NOT a new Lean-verified or Prove2Me-Proved result. The exact public interfaces of facet reduction, sub-balanced section inheritance, and the dimension-three bound are being retrieved for a small compositional formalization. Do not create an Open child of the main conjecture for this standard low-excess case.

This is a different route from positive-slack normalization. The latter supplies an explicit affine model and constructive support-preserving portals; the argument here only needs the diameter consequence and existing dimension-reduction infrastructure.

## Stronger diameter-only target

For every nonempty bounded n-row H-polyhedron P in ambient dimension d,

    n <= d + 3  ==>  DiamLE P (n - d).

Consequently n <= d + 2 implies DiamLE P 2. Redundant inequalities, zero normals, and lower-dimensional feasible sets are permitted. No strict-feasibility or irredundancy hypothesis should be introduced unless an actually used library interface requires it; the geometry itself does not.

## Ordinary proof

Induct on ambient dimension d, quantifying over n and every row presentation.

If d <= 3, the already-Proved dimension-three Hirsch theorem gives precisely the required n-d bound.

Otherwise d > 3. Since n <= d+3 < 2d, every pair of vertices shares a tight nonzero describing row. Indeed the nonzero tight normals at each vertex span the d-dimensional ambient direction space, so each tight-row set has at least d distinct rows; two disjoint sets would require n >= 2d. Equivalently, reuse the new public sub-balanced section-inheritance theorem rather than reproving this counting step.

Fix such a row i. Its equality hyperplane has an affine coordinate chart in ambient dimension d-1. Drop row i and restrict the other n-1 inequalities. The resulting H-polyhedron Q is nonempty and bounded, contains the coordinate images of both vertices as extreme points, and all its edges transport to edges of P. These are exactly the proved facet/equality-section reduction semantics; the equality section need not be a genuine facet of a full-dimensional P.

The important invariant is

    (n-1) - (d-1) = n-d,
    n-1 <= (d-1)+3.

Apply the induction hypothesis to Q. It joins the chosen endpoints in at most n-d edges/stays. Transport this same walk back to P. There is NO initial access cost, no added step, and no multiplicative recurrence: both endpoints were already in the shared equality section.

This proves the stronger n-d statement. For an empty P the padded diameter predicate is vacuous, so a version without the nonemptiness assumption follows by an empty/nonempty split.

## Why this matters for the current handoff

The positive-annihilator existence lemma is still needed to finish the explicit slack-normalization construction. It is NOT logically necessary for the desired low-excess diameter corollary once the new section-inheritance theorem is available. The earlier handoff describing normalization as the only missing route to that corollary was too narrow.

Given a bounded common-face coordinate model of ambient dimension h, select an equivalent subpresentation using m <= M_min rows. If M_min <= h+2, then m <= h+2, so the diameter-only result gives coordinate diameter <=2. Use the already-Proved intrinsic common-face coordinate transport to obtain the desired face bound. The same argument with h+3 gives a diameter-three base case. No geometric facet-count API is required for either consequence.

## Exact public dependencies to reuse

- `Hirsch.diamLE_le_section_diamLE_of_n_lt_two_d`: `0e4f233c-418a-4884-bbfb-dbfc7f76bc76`, accepted solution `19dcd669-189e-4b8c-8a39-d194439f3048`.
- `Hirsch.facet_reduction`: `11b3500a-b9f8-4b44-94aa-d71354441ddb`.
- `Hirsch.dimension_three_bound`: `cf588038-4ee8-4c90-b034-348c28d0da21`.
- Intrinsic common-face coordinate diameter transport: `d7b5f979-eb85-47c4-8c1d-a53aff0bccbe`.
- Local minimum-subpresentation witness: `HirschCircuitLocalization.commonFaceMinSubpresentation_spec` in `Solutions/PolynomialCommonFaceMinimalSubpresentation.lean`.

The publication action for the independent normal-relation certificate retrieves and preserves the first three exact live formal interfaces in `next-proof-interfaces.json`. Check the actual binders, the lower-dimensional row budget, nonzero-row requirements, and the edge-transfer conclusion before writing the Lean composition.

## Boundary

This is the classical small-excess consequence of low-dimensional Hirsch, not an improvement on the general Polynomial Hirsch bounds. Once n-d grows with dimension, the induction reaches dimension n-d rather than a universally small base case. No uniform polynomial bound for that remaining dimension has been established by this argument. It does not solve whole-walk carrier accounting or any of the current general Open leaves.
