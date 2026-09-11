# Public common-face row-excess monotonicity verification — 2026-09-11

Frozen source commit: `434028f891cde054234bfd09ff9002bc6409884f`.
Verification run: `34633943107`; job `103377193533`.
Environment: Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

The standalone public-vocabulary module `Solutions.PolynomialCommonFaceRowExcessPublic` compiled successfully. The declaration

`HirschRowExcessPublic.common_face_has_subpresentation_faceDim_add_row_excess`

has transitive axiom closure exactly within `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or additional axiom occurs.

## Statement

For a finite H-presentation with `d <= n`, any feasible source checkpoint `u`, and arbitrary point `v`, the canonical common-face coordinate H-polyhedron admits an equivalent original-row subpresentation using at most

```text
commonFaceDim a b u v + (n-d)
```

rows.

No boundedness, circuit, checkpoint-vertex, strict-feasibility, or irredundancy hypothesis appears. Thus restricting to a common carrier never increases row-presentation excess beyond the ambient row excess in this public representation sense.

The proof is self-contained over Mathlib plus `Definitions.Def_Hirsch_common_face_geometry`: common-source rows vanish on the carrier direction, the remaining effective restricted rows are disjoint from them, rank-nullity gives the dimension loss, and zero restricted rows are tautologies because the source checkpoint is feasible.

## Scope

This is a structural presentation theorem, not a diameter theorem by itself. Combined with the public small-carrier theorem `Hirsch.common_face_diameter_of_subpresentation_excess_le_three`, it immediately recovers low-ambient-excess carrier bounds. For large `n-d`, it only caps the carrier presentation excess by the same ambient excess and does not solve the general whole-walk routing problem.
