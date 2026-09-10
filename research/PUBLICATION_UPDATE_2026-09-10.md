# Prove2Me publication update — 2026-09-10

This file is a delta to `PUBLICATION_INDEX_2026-09-09.md`. The global
Polynomial Hirsch frontier is unchanged.

## Exterior-cap theorem — newly public / Proved

- Theorem: `Hirsch.simultaneous_clip_diameter_of_exterior_cap`
- Prove2Me theorem ID: `2e20b0a7-503c-4be4-bd9c-446b88f77c8e`
- Submission ID: `9e7561b5-4ca6-4e2f-acf5-d9f87f7b9d91`
- Verdict: **ACCEPTED**
- Live status: **Proved**

Formal scope: the theorem assumes an explicit compact exterior-cap witness,
strict common centre, old-vertex routing bound, and classification saying every
new cap extreme point is adjacent to an old vertex. It proves the final clipped
diameter bound `D + 1 + sum_i B_i`. It does **not** formalize existence of the
required exterior cap for every pointed H-polyhedron, and it does not prove
Polynomial Hirsch.

Verified provenance:

- source branch: `chatgpt/recession-cap-clipping` (PR #52)
- verified source commit: `5d57b93dc40d0f0917dcc99ce7a80274890c5c54`
- verification Actions run: `34412248641`
- source + standalone compilation: PASSED
- standard axiom audit: PASSED
- exact regression hashes: MATCHED
- standalone `solution.lean` SHA-256:
  `386d8c27c5c0b4926ee009095ef2e726451aba86ad3ff5140c7bf30a744a592e`

The lightweight publication test was Actions run `34426799646`. Attempt 1
published and proved the theorem; attempt 2 reused the same theorem and returned
`SKIPPED_ALREADY_PROVED`, confirming idempotency. Receipt artifacts:
`10133077367` and `10133122469`.

## Checkpoint/routing publication sweep — six newly public / Proved

Actions run `34428230806` recompiled and axiom-audited six standalone public
packets before making any authenticated publication calls. All six submissions
were **ACCEPTED** and all six live theorem statuses ended **Proved**:

| Theorem | Theorem ID | Submission ID |
|---|---|---|
| `Hirsch.face_interval_cover_route_bound_of_active_containment` | `922463d6-1e90-4897-af86-223301e92c02` | `a13d4c3a-0ef3-4515-9029-4f9b21e00623` |
| `Hirsch.compact_extreme_face_contains_parent_vertex` | `3df8730f-073f-4914-be78-64b1043b016f` | `d37135e4-7a3b-43f6-b498-20e11360066c` |
| `Hirsch.feasible_point_has_face_preserving_parent_vertex` | `0d77a819-5b23-48a2-91ba-34a6f44b49af` | `59791f2a-6b0a-4b5d-9b6b-5db6bf75845c` |
| `Hirsch.closed_extreme_faces_shared_point_has_parent_vertex` | `927effb2-313a-485a-b121-7e2cba51c753` | `0b8d54b1-9a7c-40b9-a00f-eab5519b0a4c` |
| `Hirsch.feasible_face_covered_sequence_route_bound` | `62aa8163-1166-4085-9111-b0ed6b01bf82` | `5fee4ce0-1dec-4bd1-ab2f-cc67216a5ee2` |
| `Hirsch.face_interval_cover_route_bound_of_feasible_active_containment` | `40216355-af8c-46fb-ac9a-72979288e6f3` | `5cad26a9-48d6-44ad-82d8-e757b3e498f9` |

Publication receipt artifact: `10133847456`.

These are completed theorem-level results from the PR #48/#50 checkpoint and
routing chain. Internal implementation lemmas used to prove them are not
separately registered merely to duplicate proof scaffolding.

## Separated common-face splitter — newly public / Proved

- Theorem: `Hirsch.separated_common_face_split`
- Prove2Me theorem ID: `b03857f7-3d18-4f3c-a6f8-213cb0d5d012`
- Submission ID: `79db5c58-ec42-42a5-a466-f65dbe5897d1`
- Verdict: **ACCEPTED**
- Live status: **Proved**

This is the verified PR #30 conditional splitter: under separated endpoints,
connectivity, and a uniform diameter bound `B` through dimensions `R-1`, it
reaches within `B+1` edge/stay steps a vertex whose common-face dimension with
the target is at most `d + (n - 2*d) - R`.

Publication Actions run `34429276423` first built/audited the source wrapper,
then independently compiled/audited the flattened server proof. Only standard
logical axioms were reported. The standalone packet SHA-256 was
`f82c7a821608dde939a23b86451e5367b6ea68d52941df6aead1413d9d779a68`.
Publication receipt artifact: `10133954124`.

## Publication architecture / cleanup

For the PR #52 theorem, the permanent manual workflow
`.github/workflows/prove2me-publish-exterior-cap.yml` runs on `ubuntu-slim`,
downloads the immutable previously verified artifact, validates its provenance
and proof hash, and performs only authenticated Prove2Me API work.

The checkpoint backlog and common-face splitter used temporary one-shot
publication branches because their server packets first needed independent
standalone Lean compilation. Those temporary push-triggered publication
workflow files were deleted immediately after their successful runs. They are
not persistent automatic publication paths.

## Intentionally not promoted to public Proved theorems

This publication sweep does not relabel incomplete or research-only work:

- `Hirsch.polynomial_edge_refinement_of_circuit_walks`
  (`099c6686-560c-48fc-b2c2-18b6a620a06e`) remains the genuine **Open**
  formal frontier.
- The complete radial simultaneous-clipping `L + sum_i B_i` theorem remains
  incomplete as an end-to-end Lean declaration; verified radial algebra
  components are implementation infrastructure, not a substitute for that
  missing assembly.
- PR #29 is explicitly a conditional d-step diagnostic and not a Prove2Me
  publication target in its present form.
- PR #31 contains exact rational/combinatorial research certificates rather
  than Lean hull theorems.
- PR #41/#42 retain generic repair-network helper/equivalence declarations,
  while their intended reusable public theorem-level outputs are already
  represented by `Hirsch.extreme_face_cut_route_bound`,
  `Hirsch.crossing_cube_endpoint_certificate_insufficient`,
  `Hirsch.mixed_repair_route_or_cut`, and the later start/active-containment
  theorem family.

A strict live-platform audit is run after this sweep to verify every expected
public theorem is present with status `Proved`, the stable public definitions
remain published, and the edge-refinement frontier remains `Open`.
