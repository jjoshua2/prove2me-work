# Common-face row-excess monotonicity: Prove2Me publication receipt

Authenticated publication completed 2026-09-11 on Prove2Me 0.10.1.

## Public result

- Theorem: `Hirsch.common_face_has_subpresentation_faceDim_add_row_excess`.
- Theorem ID: `eeac02bd-aa68-48e6-a246-63f921b4606d`.
- Submission ID: `e5829063-8890-484e-a67f-9a70c920ee2c`.
- Registration: **PUBLISHED**.
- Proof verdict: **ACCEPTED**.
- Final theorem status: **Proved**.
- Mission: **The Polynomial Hirsch Conjecture** (`6078cb2d-3594-44b1-a01a-fd452ddae274`).
- Mission comment: `105ee231-7cfb-467b-be7c-7fa1ce153f0d`.
- Lean: `v4.30.0`.
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

For any finite `n`-row H-presentation in ambient dimension `d` with `d ≤ n`, any feasible source checkpoint `u`, and arbitrary checkpoint `v`, let `h` be the canonical dimension of their common carrier. The canonical common-carrier coordinate H-polyhedron has an equivalent subpresentation using original restricted rows and at most

`h + (n - d)`

inequalities. Thus finite row-presentation excess does not increase under common-face restriction. No boundedness, circuit, vertex, strict-feasibility, or irredundancy hypothesis is required.

## Frozen proof provenance

- Kernel-audited source commit: `8000514edef6b0952f584b99bb0248ed8b37b5ae`.
- Source file: `Solutions/PolynomialCommonFaceRowExcessPublic.lean`.
- Source Git blob: `f0e41a15a1327e2030defc851ebb9443f8a26fb8`.
- Source SHA-256: `7695157c6bf61c87ceb9b0b6b8f5a327d0080f6471fd851eb1a50c9ec72706c2`.
- Source verification run: `34633943107`.
- Standalone publication-source commit: `4ad61f40070a592a1df99862af5f81ce1eefaf43`.
- Exact standalone `solution.lean` SHA-256: `aa0fff8625c9eb0eb7e2b890ac1e348136d0ce3283ee4c9df20b53ad6f3d5184`.
- Publication run: `34636485918`.
- Publication job: `103385521670`.
- Publication artifact: `10278431745`, `common-face-row-excess-publication`.
- Artifact size: 22,328 bytes.
- Artifact SHA-256: `ce26cf40630e6c88dc1a4fb0ace1f81c1015a34f4144ef9ea98275876fd74dd6`.

Before authentication, the final run rebuilt `Definitions.Def_Hirsch_common_face_geometry`, independently compiled the exact standalone solution, and checked its axiom report. The root declaration `solution` depends only on `propext`, `Classical.choice`, and `Quot.sound`; the repository axiom checker passed.

## Fail-closed retries

Three earlier fresh-gate attempts did not mutate Prove2Me:

1. the first standalone compile ran before the imported local definition module had been built;
2. a retry was canceled during cache restore by an unrelated pull-request event sharing the original workflow concurrency group;
3. the next retry compiled the standalone proof but omitted `#print axioms solution`, so the axiom-log checker intentionally refused to expose credentials.

The final run fixed only publication infrastructure/audit visibility. The verified theorem source and proof argument were unchanged.

## Frontier safety

The authenticated transaction read
`Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`
(`73beca40-31bc-42d5-8350-5ec9ac28bd3e`) as **Open** before and after publication.

- `frontier_graph_modified: false`.
- `new_conjectural_children: 0`.

This theorem is structural. It does not itself bound graph diameter when ambient row excess is large and does not solve whole-walk edge refinement. Its main role is to expose a stable resource: every common carrier inherits a presentation with excess at most the parent excess `n-d`.
