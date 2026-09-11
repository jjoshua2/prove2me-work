# Exact circuit-carrier deletion-savings publication receipt — 2026-09-11

## Public theorem

`Hirsch.row_circuit_selected_excess_defect_savings_identity`

- theorem ID: `c44c3313-11e2-49e0-aa41-b8acea36c29e`;
- accepted proof: `8a675045-8a44-49ae-8b6a-5389fd003a5e`;
- verdict: **ACCEPTED**;
- authenticated live status: **Proved**;
- Prove2Me version: 0.10.1;
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`;
- publication run: `34640378119`; job `103398320482`;
- publication artifact: `10279594479`, digest
  `sha256:fafebb023d0bcec20cf782d4b23f9eb3013f7ca9153c437efb57e37a0f256ca1`;
- exact submitted solution SHA-256:
  `96ddc80b130788fb6824b78b4574240140805d64adef7ae637a07321659efd78`;
- mission comment: `00a509f2-4e3c-4012-b57d-785f077f6f10`.

The theorem states an exact one-carrier accounting identity.  In a bounded
`n`-row H-polyhedron of ambient dimension `d`, for a feasible source `x`, an
ambient row-circuit displacement `y-x`, and selected effective common-carrier
rows `F` with at least the carrier dimension `h`, the full ambient row excess
`n-d` is exactly the sum of:

1. selected presentation excess `|F|-h`;
2. selected neutral-rank defect;
3. surplus disappearance of rows when restricting to the carrier;
4. omitted effective rows nonneutral on the circuit displacement; and
5. omitted neutral rows beyond the rank actually lost.

Neither checkpoint is required to be a vertex.  This is static local accounting,
not a theorem that these savings telescope along a walk or that a high-excess
carrier has short graph diameter.

## Verification and publication boundary

The reusable public-vocabulary source was integrated at commit
`ed33edd69aa9a25129b31a8448ef3303abb29b4e` after the normal hosted repository
build/axiom gate succeeded in run `34639229285`, job `103394556732`.  Its public
declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`.

The authenticated publication gate independently rebuilt a source-faithful
standalone `solution` from that frozen source, treating only the public
Definitions modules as platform imports.  No `Theorems.*` proof stub or tracked
Open theorem was imported.  The root-level `solution` compiled and passed the
axiom audit before `PROVE2ME_API_KEY` was exposed.

The first staging attempt failed closed at standalone wrapper parsing before
authentication; it registered or submitted nothing.  The clean retry passed the
standalone gate, authenticated preflight, theorem registration, server proof
verification, live theorem readback, and mission linkage.

## Frontier discipline

Immediately before and after the accepted proof,
`Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`
(`73beca40-31bc-42d5-8350-5ec9ac28bd3e`) was authenticated **Open** on the same
Mathlib revision.  The receipt records:

- `frontier_graph_modified: false`;
- `new_conjectural_children: 0`.

The next source work connects this exact equality/saturation structure to
maximal-step blockers and phase order; it should not be described as a solution
of Polynomial Hirsch.