# Prove2Me publication update — 2026-09-10

This file records the first publication using the lightweight publish-only path.
It is a delta to `PUBLICATION_INDEX_2026-09-09.md`; the global Polynomial Hirsch
frontier is unchanged.

## Newly public / Proved

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

## Verified source provenance

The submitted proof came from the immutable audit artifact produced before
publication:

- source branch: `chatgpt/recession-cap-clipping` (PR #52)
- verified source commit: `5d57b93dc40d0f0917dcc99ce7a80274890c5c54`
- verification Actions run: `34412248641`
- source + standalone compilation: PASSED
- standard axiom audit: PASSED
- exact regression hashes: MATCHED
- standalone `solution.lean` SHA-256:
  `386d8c27c5c0b4926ee009095ef2e726451aba86ad3ff5140c7bf30a744a592e`

## Lightweight publication path

Publication no longer rebuilds Lean/Mathlib. The permanent manual workflow is:

`.github/workflows/prove2me-publish-exterior-cap.yml`

It runs on `ubuntu-slim`, downloads the immutable verified artifact from run
`34412248641`, validates the source commit, environment pin, scope marker,
audit record, and proof hash, then uses the repository `PROVE2ME_API_KEY`
secret only for the Prove2Me API calls.

Publisher script:

`scripts/publish_verified_exterior_cap.py`

Live publication test:

- Actions run: `34426799646`, attempt 1
- theorem registration: PUBLISHED
- Prove2Me verdict: ACCEPTED
- final theorem status: Proved
- publication receipts artifact: `10133077367`

Idempotency test:

- same Actions run, attempt 2
- registration: REUSED
- status: Proved
- verification: `SKIPPED_ALREADY_PROVED`
- idempotency receipts artifact: `10133122469`

The temporary push-triggered bootstrap workflow used only to exercise this path
was deleted immediately afterward. The permanent publisher is manual-only.
