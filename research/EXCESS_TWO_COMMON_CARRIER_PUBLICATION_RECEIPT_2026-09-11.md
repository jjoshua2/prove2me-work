# Excess-two arbitrary-checkpoint common-carrier publication receipt — 2026-09-11

## Public theorem

`Hirsch.common_face_diameter_two_of_rows_le_dim_add_two`

- theorem ID: `ca4c980f-86d7-4810-be9e-30e473b9dd70`;
- accepted submission: `b9d5af5b-51d3-48dd-b008-a365a18b053e`;
- verdict: **ACCEPTED**;
- authenticated live theorem status: **Proved**;
- Prove2Me version: 0.10.1;
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`;
- corrected public solution SHA-256:
  `09d4118a00bd35f58879847f0cc5b2ba9a774c798dcf120dcc42887bb2e55f3d`;
- source compact-driver commit:
  `d85e9ff15194bd413c5f7e71e6f1f10e2b98697c`;
- accepted publication/recovery run: `34628673562`;
- mission comment: `b3feca04-21d1-481a-989f-76638bb21122`.

The theorem states that for a bounded `n`-row H-polyhedron in ambient dimension
`d`, if `n <= d+2` and `u` is any feasible checkpoint, then for every point
`v` the intrinsic common carrier `HirschCommonFace.commonFace a b u v` has
padded vertex-edge graph diameter at most two. The second checkpoint need not
be feasible or a vertex. Empty/lower-dimensional carriers, redundant rows, and
zero-normal tautologies are allowed.

This is a low-ambient-excess carrier result. It does **not** assert that arbitrary
carriers in general Polynomial Hirsch instances have row excess at most two.

## Local kernel evidence

The stronger repository source was first kernel checked in
`Solutions/PolynomialCommonFaceExcessTwoCarrier.lean` at frozen source
`c0ebc8fbcb69ce142420e25c6ec453c5e825d897`, run `34622809824`, job
`103340631565`. All three new declarations used only `propext`,
`Classical.choice`, and `Quot.sound`.

For server publication a smaller composition driver was independently checked at
commit `d85e9ff15194bd413c5f7e71e6f1f10e2b98697c`. Run `34627787693`, job
`103356976904`, compiled both requested declarations and again found only the
three standard logical axioms.

The compact proof re-establishes the effective common-face row count and
coordinate boundedness from public common-face definitions, then takes two
already-Proved results as explicit premises:

1. `Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three`, theorem
   `12426807-9602-4014-bd5e-c69fb43f4cb6`;
2. `Hirsch.common_face_diamLE_of_coord_diamLE`, theorem
   `d7b5f979-eb85-47c4-8c1d-a53aff0bccbe`.

The authenticated publisher checked both dependency names, exact formal
statements, live `Proved` statuses, and Mathlib pins before verification.
No Open theorem or sketch was imported.

## First packaging failure and safe recovery

The theorem registration itself succeeded on the first publication run
`34628073766`, yielding the same theorem ID above. Its first proof submission
`5b5cfeb8-2bc8-4d3e-992d-492f2011d3ae` received `WA` only because the generated
proof declared `Hirsch.solution` inside `namespace Hirsch`; the verifier expects
a root-level declaration named exactly `solution`.

No duplicate theorem was registered. The retry changed only that wrapper shape,
reused the existing Open theorem, re-ran the compact Lean/axiom gate and
authenticated dependency checks, and submitted proof
`b9d5af5b-51d3-48dd-b008-a365a18b053e`, which was ACCEPTED and changed the
live theorem to Proved.

## Frontier discipline

Immediately before and after the accepted proof, the active high-dimensional
edge-refinement theorem

`Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`
(`73beca40-31bc-42d5-8350-5ec9ac28bd3e`)

remained **Open** on the same Mathlib pin. The publication created no
conjectural children and did not modify the theorem graph.

The mathematical next step is whole-walk composition: combine this uniform
`DiamLE <= 2` carrier bound with the already kernel-checked feasible-checkpoint
face-routing machinery. That can yield a `2L` ordinary edge/stay refinement for
length-`L` feasible checkpoint sequences in the same ambient excess-two regime,
without assuming intermediate checkpoints are vertices.
