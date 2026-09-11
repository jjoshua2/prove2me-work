# Polynomial Hirsch: bidirectional Prove2Me synchronization — 2026-09-11

## Scope

This receipt records a status synchronization between repository
`jjoshua2/prove2me-work` and the live Prove2Me mission **The Polynomial Hirsch
Conjecture**. It is a collaboration/status transaction, not a new theorem,
proof-sketch, or theorem-graph decomposition.

- Mission ID: `6078cb2d-3594-44b1-a01a-fd452ddae274`.
- Platform observed: Prove2Me **0.10.1**.
- Mathlib revision: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- Final status-only writeback checked at `2026-09-11T15:28:40.516371+00:00`.

## Prove2Me → GitHub readback

Authenticated readback run:

- Actions run `34615484039`;
- job `103316231627`;
- artifact `10269974221`, `prove2me-hirsch-sync-readback`;
- artifact SHA-256
  `4edd1398af347e0e4c6e6e85134fad5d17e57fee7ed416e6f103fcd5b1187bef`.

The API exposed six curated milestones through the live mission milestone
endpoint. All six were **Proved**:

1. Klee/Klee--Walkup, dimension at most three;
2. Larman's exponential diameter bound;
3. Naddef's `0/1`-polytope result;
4. Kalai--Kleitman quasi-polynomial bound;
5. Todd's sharpening;
6. the Santos counterexample to the original linear Hirsch conjecture.

The readback also found repository work that had already reached Prove2Me but
had not yet been reflected in `main`: `Hirsch.injective_affine_image_diameter_iff`
was live **Proved** with theorem ID
`c4b0c852-981b-4bd7-8578-07e72315c3c9` and accepted solution
`d0300dfb-691d-4388-8d4d-878c28b9cddf`. The corresponding audited GitHub
source was subsequently merged through PR #90.

The newest board research log also supplied progress from outside the stale
repository status snapshot:

- `Hirsch.diamLE_le_section_diamLE_of_n_lt_two_d`
  (`0e4f233c-418a-4884-bbfb-dbfc7f76bc76`) is **Proved**, accepted solution
  `19dcd669-189e-4b8c-8a39-d194439f3048`;
- `Hirsch.polynomial_access_to_ridge_visible_vertex`
  (`5f309362-bbda-4dea-806f-20b4e2712a2d`) remains **Open**;
- experiments on duals of stacked simplicial polytopes show ridge-visible
  distance is not uniformly `O(1)`; a naive recurrence paying whole facet
  diameter becomes dimension-multiplicative;
- additional public toolkit now includes product-diameter, box-diameter,
  vertex-listing, common-face `0/1`, and synchronized scalar-height edge
  results.

## GitHub → Prove2Me writeback

A fail-closed owner-only workflow re-read all relevant states and posted one
idempotently marked mission comment.

Successful writeback:

- Actions run `34616328714`;
- job `103319073555`;
- artifact `10271410433`, `prove2me-hirsch-sync-writeback`;
- artifact SHA-256
  `90302a55b4ba91b01792ae0d5cf7be269d9382567c5f1538734b4f2a57c93ca2`;
- mission comment ID `0d87f2f5-42c6-45cb-ad21-6ba88a670dfd`;
- idempotence marker `<!-- jjosh-hirsch-sync-2026-09-11-1520z -->`.

Two earlier writeback attempts failed closed before posting: the first assumed
the mission occurred on the first `/missions` page; the second tried a direct
GET endpoint that Prove2Me 0.10.1 answers with HTTP 405. The successful run
uses the same paginated mission lookup that had already succeeded during
readback. No duplicate sync comment was created.

Before and after posting, the workflow required the following exact live
states on the pinned Mathlib revision:

| Theorem | ID | Live status |
| --- | --- | --- |
| `Hirsch.polynomial_hirsch_conjecture` | `58eae2c9-6fd5-4d5d-8aa7-6d552ad80bac` | **Open** |
| `Hirsch.polynomial_edge_refinement_of_circuit_walks` | `099c6686-560c-48fc-b2c2-18b6a620a06e` | **Open** |
| `Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four` | `73beca40-31bc-42d5-8350-5ec9ac28bd3e` | **Open** |
| `Hirsch.common_face_diameter_of_dim_ge_six` | `87a8b4f4-8b58-4340-8cb9-5fd1b548d01e` | **Open** |
| `Hirsch.polynomial_access_to_ridge_visible_vertex` | `5f309362-bbda-4dea-806f-20b4e2712a2d` | **Open** |
| `Hirsch.irredundant_rows_card_le_any_equivalent_presentation` | `8538150b-8afe-47ad-94b0-d72189b80264` | **Proved** |
| `Hirsch.normalized_two_moment_slice_diameter_two` | `e93edd7b-4659-4df5-9eab-fbcce4352c78` | **Proved** |
| `Hirsch.injective_affine_image_diameter_iff` | `c4b0c852-981b-4bd7-8578-07e72315c3c9` | **Proved** |
| `Hirsch.diamLE_le_section_diamLE_of_n_lt_two_d` | `0e4f233c-418a-4884-bbfb-dbfc7f76bc76` | **Proved** |

The before/after theorem snapshots were byte-for-byte equal at the JSON summary
level. The receipt explicitly records:

- `graph_mutation: false`;
- `theorem_or_proof_submission: false`.

No new theorem was registered because the strongest audited repository results
that should be public — the two-moment theorem and injective affine transport —
were already live **Proved**, so another submission would have been a duplicate.

## Status communicated to collaborators

The mission comment states:

- all six curated milestones are Proved, while the Polynomial Hirsch root is
  still Open;
- the row-count, normalized two-moment, and injective affine transport results
  are public Prove2Me facts and their source status is synchronized in GitHub;
- the new sub-balanced section theorem was pulled back from the live board for
  reuse;
- the current repository target is positive-weight/codimension-two slack
  normalization, aiming for the interface
  `M_min ≤ h + 2 ⇒ intrinsic common-face diameter ≤ 2`;
- that normalization is **not** yet kernel-verified or submitted;
- high-dimensional common-face diameter, ridge-visible access, circuit-to-edge
  refinement, and the root conjecture remain Open;
- no new conjectural child was created.

## Current mathematical handoff

The graph-semantics side of the low-excess program is now public:

1. normalized two-moment slices have diameter at most two;
2. injective affine embeddings preserve/refect the exact graph diameter.

The remaining bridge is therefore to prove in Lean that the relevant bounded
low-row-count H-presentations have exactly such a slack image. The ordinary
proof plan is recorded in
`research/EXCESS_TWO_SLACK_NORMALIZATION_BRIDGE_2026-09-11.md`; it should not be
reported as Proved until the Lean and publication gates pass.
