# Face-cover publication receipt — 2026-09-10

Authenticated Prove2Me verdicts for the four rank/weighted face-cover
theorems published from PR #62. Platform **0.9.9**. Environment Lean
`v4.30.0` / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

The GitHub publication workflow `34539939870` compiled, axiom-audited, and
authenticated, then hit the 35-minute job timeout during
register/verify. The four theorems nevertheless reached live **Proved**
status; this file records the IDs from an authenticated API read after
that run.

Frozen source: PR #61 commit `681314640b6f84792d8ae011c3534a6e8c456930`,
Actions run `34532572816`. Exact blobs transplanted onto `main` by PR #66
merge `5a731041dc8c785e362209cead85051f6fa44557`.

| Theorem | Theorem ID | Accepted submission | Live status |
|---|---|---|---|
| `Hirsch.weighted_geodesic_face_cover_diameter_bound` | `7815b37c-dab5-42b8-a1ed-fbb08d1eab5b` | `35f52f45-7fcb-47f4-9213-c5c947e6ff63` | Proved |
| `Hirsch.tight_rows_outside_subspace_cardinality_bound` | `27bd88d2-6943-4ca3-abbd-170264c17b98` | `d81b3bfc-ac7a-4ce5-9308-cd2746724c0d` | Proved |
| `Hirsch.rank_selected_row_face_diameter_bound` | `76cdff62-bb43-4758-a1ed-980ce0ec5230` | `c227d208-25c5-48b1-b49b-e94788770bf1` | Proved |
| `Hirsch.weighted_cover_improvement_requires_smaller_child` | `599aaead-0333-4d91-8bc5-d7e3e8b9831a` | `65314a03-5c93-470f-8fc9-820209f34901` | Proved |

These results keep child-diameter or covering-weight hypotheses explicit.
They do not prove polynomial edge refinement. Rank-selected sections are
not claimed proper for an arbitrary normal subspace. The averaging barrier
is a finite counting theorem, not a graph-diameter lower bound.

Machine-readable copy: `research/face_cover_publication_receipt.json`.

Also recorded in the same authenticated read:

- `Hirsch.row_circuit_step_adj_of_common_face_dim_le_one`
  (`f8d8878c-aaf0-4b1e-8b93-904e25be3871`, ACCEPTED
  `cffbbaeb-ace8-4ab6-9659-9ce45700cc14`, **Proved**), the public adapter
  of the PR #63 carrier-to-edge theorem.

Live open leaf of `Hirsch.polynomial_hirsch_conjecture`:

`Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`
(`73beca40-31bc-42d5-8350-5ec9ac28bd3e`).
