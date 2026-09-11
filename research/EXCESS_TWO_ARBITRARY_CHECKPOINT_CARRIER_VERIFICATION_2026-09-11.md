# Excess-two arbitrary-checkpoint carrier verification — 2026-09-11

## Kernel result

Frozen source commit: `c0ebc8fbcb69ce142420e25c6ec453c5e825d897`.
Verification run: `34622809824`; job `103340631565`.
Artifact: `excess-two-carrier-audit`, ID `10273123214`, ZIP SHA-256
`6a25917dca32920acceb0880dc40cbe67112c0ff3d78e8b16b6c582dfbe9e3c9`.

Environment: Lean 4.30.0 / Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

The targeted build completed successfully. The following three declarations
were each audited with transitive axiom closure exactly
`[propext, Classical.choice, Quot.sound]`:

1. `HirschCircuitLocalization.commonFace_diamLE_two_of_subpresentation_at_most`;
2. `HirschCircuitLocalization.commonFace_has_subpresentation_dim_add_two_of_rows_le_dim_add_two`;
3. `HirschCircuitLocalization.commonFace_diamLE_two_of_rows_le_dim_add_two`.

No `sorryAx` or other axiom occurs in their transitive closures.

## Mathematical content

The first theorem says any common carrier whose canonical coordinate
H-polyhedron has an equivalent presentation with at most `h+2` rows has
intrinsic padded graph diameter at most two, assuming the public small-excess
H-polyhedron bound.

The second theorem is independent of endpoint extremality: in an ambient
`n`-row H-presentation with `n <= d+2`, every common-face coordinate model based
at a feasible source checkpoint has such an `h+2`-row equivalent
subpresentation. It deletes precisely the rows whose restricted coordinate
normals vanish and uses the already-checked effective-row count inequality.

Combining them gives the whole local carrier statement: for any feasible
checkpoint `u` and arbitrary `v`, if the bounded parent has `n <= d+2`, then

```text
DiamLE (commonFace a b u v) 2.
```

This is an intrinsic graph bound for the carrier itself; the checkpoints need
not be carrier vertices.

## Evidence boundary

The local source leaves `SmallExcessHpolyBound` as an explicit logical premise,
so the kernel audit does not import a theorem stub. An unconditional public
composition may discharge this premise with the already-Proved
`Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three`
(theorem `12426807-9602-4014-bd5e-c69fb43f4cb6`).

This remains a low-ambient-excess result. It does not assert that arbitrary
circuit carriers in general Polynomial Hirsch instances have excess <=2, and
it does not by itself sum routing cost over a whole circuit walk.
