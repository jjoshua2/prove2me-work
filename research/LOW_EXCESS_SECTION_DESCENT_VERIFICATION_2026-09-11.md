# Low-excess section descent: kernel verification — 2026-09-11

## Actual verification

- Frozen source commit: `2774702c54078cb8efae7bed185ed1b4b93bce5b`.
- Source module: `Solutions/PolynomialLowExcessSectionDescent.lean`.
- Source blob: `794126103cc9d9f60a95eb262d96d282f3e9ad4f`.
- Actual vertex-span proof dependency blob: `673e5a68f154b66556d01dd81977107329a3415e`.
- Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- Verification run: `34619780682`; job: `103330569162`.
- Source module compiled successfully at `2026-09-11T16:05:05Z` on its first check.
- Independent flattened driver and adapter compiled successfully at `2026-09-11T16:05:13Z`.
- Four required declarations, five printed reports, all using only `propext`, `Classical.choice`, and `Quot.sound`.

Driver SHA-256:
`d58e8dcb92d9ee1d21f330a64432c6b0d7b880ba6c44c803dd39bf33bc0deb1a`.

Prepared public composition SHA-256:
`58ceb59004e1f9046ccaaf8b55ae39e7e8646135c5c521b8e74b495e7c238568`.

Preserved artifact: `10272455557`, `low-excess-descent-final-proof`.
Artifact SHA-256: `dd623f2a3a6b8e365ad7416a14011edc699260ef068b184aef754d52d7afbdae`.

The original monitor was canceled at 16:08:53 UTC after the kernel audit and authenticated preflight succeeded. This does not invalidate those completed checks, and does not establish whether an outstanding platform registration or submission subsequently completed. Replacement monitoring run `34620239467` was still active at this receipt's writing. Inspect its exact platform receipt before reporting public acceptance; do not re-register or resubmit merely because a GitHub monitor was canceled.

## Audited declarations

1. `HirschLowExcess.dimension_le_tightNonzeroRows_card`.
2. `HirschLowExcess.vertices_share_nonzero_tight_row_of_n_lt_two_d`.
3. `HirschLowExcess.hpoly_diameter_le_excess_from_proved_inputs`.
4. Independent `checked_low_excess_adapter`.

The fifth printed report is the actual finite-perturbation vertex-span proof.

## What is proved by the audited driver

Let the two explicit propositions `LowDimensionalHirsch` and `FacetWalkReduction` hold. They are precisely the types of the two already-Proved platform theorems below. The driver then proves, for every bounded n-row H-polyhedron P in ambient dimension d,

```
n <= d + 3  ==>  DiamLE P (n - d).
```

No strict feasibility, irredundancy, or nonemptiness assumption is added. The driver imports actual local proof source, not platform theorem stubs; the two established geometric results are explicit logical premises in this kernel audit.

The public composition supplies those premises through the platform's tracked imports of:

- `Hirsch.dimension_three_bound`, theorem `cf588038-4ee8-4c90-b034-348c28d0da21`;
- `Hirsch.facet_reduction`, theorem `11b3500a-b9f8-4b44-94aa-d71354441ddb`.

Both exact statements, Proved statuses, and Mathlib pins were checked by authenticated retrieval. Their interfaces were saved by read-only run `34618676750`, artifact `10271575466`. A Prove2Me ACCEPTED/live Proved receipt is still separately required for the unconditional published composition. Do not describe a local import of theorem stubs as an axiom-clean proof of that unconditional composition.

## Mathematical proof and interface corrections

Each vertex has at least d distinct tight nonzero row normals, because evaluation on those normals is injective by the proved vertex-span argument. With n<2d, any two such tight-row sets intersect. The common row is genuinely nonzero; tautologies cannot supply it.

Induct on ambient dimension. For d<=3, apply the low-dimensional Hirsch theorem, handling the empty set vacuously. For d>3, n<=d+3 implies n<2d. The endpoints share a nonzero tight row and remain extreme in its equality section. Facet reduction deletes that row and reduces ambient dimension by one. The induction hypothesis applies with the same excess:

```
(n-1) - (d-1) = n-d.
```

Both endpoints were already in the equality section, so no access step or multiplicative routing cost is introduced.

The newer sub-balanced inheritance theorem was the useful clue, but its actual premise requests intrinsic bounds for ALL describing-row sections, including zero-row tautologies. The actual facet-reduction theorem returns an ambient edge walk, not necessarily a walk certified to remain in the section. The driver avoids an invalid composition: it proves the nonzero common-row fact directly, and uses precisely the ambient-walk conclusion that facet reduction provides.

## Consequences and limits

The mathematical result gives diameter <=2 for n<=d+2 and <=3 for n<=d+3 without positive normalization-weight existence. Combining it with a small equivalent common-face row presentation and intrinsic coordinate transport yields the intended low-excess face consequence; that final common-face adapter has not been written or checked in this module.

This is the classical small-excess consequence of low-dimensional Hirsch. It does not give a fixed-exponent polynomial bound for arbitrary excess, resolve high-dimensional common-face diameter, or bound total circuit-to-edge routing cost.

All compilation in this receipt was hosted. The editing conversation's local runtime was unavailable due to attachment-mount transport timeouts; no local Lean success is claimed.
