# Prove2Me publication: vertex slack-row bound

Date: 2026-09-12.

Public theorem: `Hirsch.vertex_strictly_slack_rows_card_le_row_excess`.

## Platform result

- theorem ID: `804b7a8e-0572-4407-a014-2d9f4aaa6f87`
- proof submission ID: `8dc241ef-cb1e-4eec-9423-a424b559d380`
- verdict: **ACCEPTED**
- live theorem status: **Proved**
- platform version: `0.10.3`
- Mathlib revision: `c5ea00351c28e24afc9f0f84379aa41082b1188f`
- publication run: `34690693356`
- job: `103545273814`
- artifact: `10296768996`
- artifact digest: `sha256:f2c752542f3e48eb7b88c99a88cdf0c949ec0e6c9bd24c9d82c04a28b9086ea7`
- submitted standalone proof SHA-256: `fc28c6c08d15ce5add750e1ea08f25d7661bfcdef052b70d66ff13ebbbc67821`
- mission: `The Polynomial Hirsch Conjecture`, ID `6078cb2d-3594-44b1-a01a-fd452ddae274`
- mission comment ID: `0ef6749c-8ba2-4454-971c-8f488c397774`

## Exact source provenance

Corrected mathematical source commit:
`e0b81dae6030e583438007c48901e76232ec33cf`.

Source path:
`Solutions/PolynomialVertexSlackRowsPublic.lean`.

Source Git blob:
`2a1fab2bf0c24ad8dae878ded46848d61617bf79`.

The generated standalone `solution.lean` imports only Mathlib plus the public `Definitions.Def_Hirsch_model`; it has no tracked private theorem dependency. The repository source and the generated standalone proof were both compiled and transitive-axiom-audited before the repository secret became available to the authenticated step. Only `propext`, `Classical.choice`, and `Quot.sound` occur.

## Statement and proof

Every vertex of an `n`-row H-presentation in dimension `d` has at most `n-d` strictly slack describing inequalities. Equivalently, at least `d` rows are tight at every vertex. No boundedness, irredundancy, simplicity, or full-dimensionality assumption is used.

The proof gives a direct finite-perturbation argument that the tight row normals span ambient directions. The evaluation map against tight normals is therefore injective, so finite-dimensional rank gives at least `d` tight row indices. Feasibility partitions the `n` rows into tight and strictly slack indices, yielding the result.

## Controlled publication history

The first publication workflow attempt stopped in immutable-source preflight because a shallow checkout did not contain the frozen source commit. No Lean proof and no credential use occurred.

After changing the checkout to full history, the second attempt reached Lean but exposed one finite-set membership normalization error in the public proof. The secret-bearing step remained unexecuted and no Prove2Me mutation occurred. The source was repaired exactly at that point, frozen at the commit above, and the final controlled run succeeded.

The successful run compiled and audited the corrected source and exact standalone packet before authentication, then registered the theorem, submitted the proof, received `ACCEPTED`, observed live `Proved`, mission-linked the result, and performed the authenticated frontier audit. The temporary secret-bearing workflow was removed afterward.

## Frontier audit

Authenticated reads immediately before and after publication both found:

- theorem: `Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`
- theorem ID: `73beca40-31bc-42d5-8350-5ec9ac28bd3e`
- status: **Open**
- Mathlib revision: `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The publication client reported `frontier_graph_modified: false` and `new_conjectural_children: 0`.

This theorem is the sharp cardinality input behind the target-anchored batch-reinsertion bound. It does not supply final face-routing budgets and does not prove Polynomial Hirsch.
