# Small common-carrier presentation-excess publication receipt — 2026-09-11

## Public theorem

`Hirsch.common_face_diameter_of_subpresentation_excess_le_three`

- theorem ID: `d42af13a-a00d-4a15-b22f-19abc4f49276`;
- accepted proof: `5747cb24-6297-4efe-bb48-c25a525a8702`;
- verdict: **ACCEPTED**;
- authenticated live status: **Proved**;
- Prove2Me version: 0.10.1;
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`;
- publication run: `34631322926`;
- artifact: `common-face-small-carrier-publication`, ID `10275899730`;
- artifact digest: `sha256:1749254b705e8427866e961106d964e8b9869abba23253eeff8315ca9a876ca9`;
- mission comment: `09785f86-3f34-40dc-92c8-05c114231e1c`.

The theorem states: if a bounded common carrier has canonical coordinate
dimension `h` and admits an equivalent original-row coordinate H-presentation
using at most `h+r` rows with `r <= 3`, then its intrinsic padded vertex-edge
graph diameter is at most `r`. The checkpoints need not be vertices, and the
ambient parent may have arbitrary row excess.

## Proof architecture

The compact public driver was independently kernel-checked in run
`34630858124`, job `103367056989`, at source commit
`732a3d13258662977d110642e093fdf94aea9528`. Its only public declaration uses
only `propext`, `Classical.choice`, and `Quot.sound`.

The submitted root-level `solution` composes that audited driver with exactly
two already-Proved dependencies, both authenticated for exact theorem name,
formal statement, live `Proved` status, and Mathlib pin before submission:

1. `Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three`
   (`12426807-9602-4014-bd5e-c69fb43f4cb6`);
2. `Hirsch.common_face_diamLE_of_coord_diamLE`
   (`d7b5f979-eb85-47c4-8c1d-a53aff0bccbe`).

The proof applies the first theorem to the supplied `m <= h+r <= h+3`
coordinate subpresentation, pads its `m-h` graph walk to length `r`, identifies
that presentation with the full common-face coordinate H-polyhedron, and then
uses the second theorem to transport the genuine graph walk into the intrinsic
common carrier.

No Open theorem, sketch, or conjectural child is imported.

## Frontier discipline

Immediately before and after the accepted proof,
`Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`
(`73beca40-31bc-42d5-8350-5ec9ac28bd3e`) remained **Open** on the same Mathlib
pin. The theorem supplies a reusable local cost rule; it does not assert that
arbitrary circuit carriers have presentation excess <=3.

The stronger repository reduction
`feasible_sequence_edge_route_of_carrier_excess_budgets_le_three` is also
kernel-verified: if each step carrier supplies an explicit budget `R i <= 3`
and an `h_i + R i` equivalent presentation, the parent edge/stay route has exact
budget `sum_i R i`. Bounding or amortizing those carrier excesses in the general
whole-walk problem remains the open task.
