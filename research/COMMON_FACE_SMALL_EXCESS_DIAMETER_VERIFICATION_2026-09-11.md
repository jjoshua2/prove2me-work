# Common-face small-excess diameter adapter verification — 2026-09-11

## Result

The source theorem

`HirschCircuitLocalization.commonFace_diamLE_two_of_minCount_le_dim_add_two`

was kernel-compiled and transitive-axiom audited at frozen source commit
`6d6b194584e479f8593fdeb76a77ac0ae5df8c0d`.

Verification run: `34621838819`, job `103337443279`.
Artifact: `common-face-small-excess-audit`, ID `10272472901`, uploaded ZIP
SHA-256 `f30f4e325f48b109d88804b3926e23eb01080d4d6a66ea15b04fa169b50cd919`.

Environment:

- Lean 4.30.0;
- Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

The job reports `Build completed successfully (8501 jobs)`; that count includes
cached dependencies and is not a count of newly authored results.

## Audited declarations

All three requested declarations depend only on `propext`, `Classical.choice`,
and `Quot.sound`:

1. `HirschCircuitLocalization.commonFaceAffineMap_injective`;
2. `HirschCircuitLocalization.commonFaceAffineMap_image_coord`;
3. `HirschCircuitLocalization.commonFace_diamLE_two_of_minCount_le_dim_add_two`.

No `sorryAx` or other axiom appears in their transitive closures.

## Mathematical statement audited locally

The adapter keeps the public small-excess H-polyhedron theorem as an explicit
logical premise `SmallExcessHpolyBound`. Given a bounded parent H-polyhedron,
ambient vertices `u,v`, and

```text
commonFaceMinSubpresentationCount a b u v
  <= commonFaceDim a b u v + 2,
```

it proves intrinsic

```text
DiamLE (commonFace a b u v) 2.
```

The proof obtains the existing irredundant/strict common-face coordinate model,
uses presentation-independent minimum row count to identify its row count,
applies the assumed small-excess bound to that bounded coordinate H-polyhedron,
pads its `m-h <= 2` walk, and transports actual graph adjacency through the
injective affine common-face chart.

Thus the local audit verifies the new common-face geometry/transport adapter
without importing a theorem stub. The unconditional public composition is a
separate platform step: it must discharge `SmallExcessHpolyBound` with the
already-Proved theorem
`Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three`
(theorem `12426807-9602-4014-bd5e-c69fb43f4cb6`).

## Scope

This is a local carrier theorem. It does not assert that arbitrary circuit
carriers have intrinsic row excess at most two, does not bound the number of
expensive carriers in a whole circuit walk, and does not close Polynomial
Hirsch or its d>=4 circuit-edge-refinement leaf.
