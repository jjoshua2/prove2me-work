# High-excess independent-row-block routing: Prove2Me publication receipt

Authenticated publication completed 2026-09-11 on Prove2Me 0.10.1.

## Public result

- Theorem: `Hirsch.hpoly_diameter_le_excess_of_independent_small_row_blocks`.
- Theorem ID: `27737675-3725-4a3d-92d7-92a87e91031e`.
- Accepted submission: `78085f91-e27d-4a2d-90ed-5c646a38f8ae`.
- Registration: **REUSED** (the theorem had been registered by the prior fail-closed proof attempt).
- Proof verdict: **ACCEPTED**.
- Final theorem status: **Proved**.
- Mission: **The Polynomial Hirsch Conjecture** (`6078cb2d-3594-44b1-a01a-fd452ddae274`).
- Mission comment: `d27715fd-94c0-42a3-8a25-3da83332e099`.
- Lean: `v4.30.0`.
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

Statement: a nonempty bounded `n`-row H-polyhedron in dimension `d` has padded ordinary vertex-edge diameter at most `n-d` whenever an explicit invertible linear coordinate certificate splits the complete row presentation into independent blocks and every block has row excess at most three. There is no bound on the total row excess or number of blocks.

This is a genuine high-excess ordinary-edge routing theorem. It relies on actual Cartesian-product structure, not on static deletion savings or a carrier-count argument.

## Public dependency

The unconditional Prove2Me proof composes the source-faithful row-block driver with the already-Proved theorem

`Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three`

- theorem ID `12426807-9602-4014-bd5e-c69fb43f4cb6`;
- status re-read as **Proved**;
- exact formal statement and Mathlib pin checked before submission.

The publication driver itself was independently kernel/axiom audited with that theorem represented only as an explicit premise. The driver depends only on `propext`, `Classical.choice`, and `Quot.sound`.

## Frozen source provenance

- Source PR: #132.
- Source commit: `4924c6ea81cda80c6a8bd54ce2a0d3d784525b3b`.
- Product-walk source blob: `64e5977f9cd5fd9617b67e82f504550236d49b83`.
- Affine-transport source blob: `ada90a58fe876f5e0b31ec20a0f8c22b1c408dd1`.
- Row-block source blob: `f410f77d854bf2853372492965d35561695f885b`.
- Hosted source verification: run `34642959632`, job `103406870271`; see `research/HIGH_EXCESS_ROW_BLOCK_HOSTED_VERIFICATION_2026-09-11.md`.
- Dependency-free publication driver SHA-256: `e5b67e8f31f3698db54011c1d4f492aa92e6b7ec2d785c0326556ab286ea071d`.
- Accepted root-level solution SHA-256: `e963ae734869955cc55f5166b5d2092c77e80d617fc77ccf7fcdc26694e4a5ec`.
- Publication run: `34644738674`.
- Publication job: `103412860556`.
- Publication artifact: `10282096832`, `high-excess-row-block-publication`.
- Artifact SHA-256: `ab4299d061fcb2ea47a1779ce5bc36525f64253295863a4e1062c973805b2d35`.

## Fail-closed publication history

Two infrastructure/proof-wrapper failures preceded acceptance and did not establish a false proof claim:

1. Run `34643820723` failed before authentication because `Definitions.Def_Hirsch_model` had not been built before direct compilation of the generated driver.
2. Run `34644132950` passed driver compilation/axiom audit and authenticated preflight, registered the target theorem, but submission `14382e80-77be-4026-85af-41b3ada2e0fe` received WA with exactly `Unknown identifier solution`. The uploaded file defined `Hirsch.solution`; Prove2Me requires the distinguished declaration at the root. The retry changed only that wrapper scope.

The final run reused the same registered target theorem and the same audited driver/mathematical proof.

## Frontier safety and strategic boundary

The authenticated transaction read

`Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`
(`73beca40-31bc-42d5-8350-5ec9ac28bd3e`)

as **Open** both before and after publication.

- `frontier_graph_modified: false`.
- `new_conjectural_children: 0`.

This theorem directly resolves many high-excess carriers, including product/cube-style zero-savings examples once redundant carrier rows are certified away. It does **not** assert that every circuit carrier factorizes. The remaining hard case is a genuinely coupled minimum carrier containing at least one residual block of excess four or more, or a cost-controlled bypass of such a carrier.
