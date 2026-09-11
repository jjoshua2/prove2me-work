# Prove2Me 0.10.0 publication audit — 2026-09-10

Final authenticated integration audit for the Polynomial-Hirsch working set.

- Actions run: `34556446047`
- job: `103130020027`
- source head audited: `6938fd584f2e5e08a6a69ba69fb1e3e36169588d`
- artifact: `10182786856`
- artifact digest: `sha256:4492f3124aeba807cb5a8e5f7e5feb81523b92dbaa14b39a6a4eb65ee8a9d6b8`
- Prove2Me version required and observed: `0.10.0`
- environment: Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The gate first compiled the exact integrated circuit-step characterization source and both public adapters and audited their `solution` declarations. It then authenticated with the repository `PROVE2ME_API_KEY` and ran `scripts/audit_prove2me_publications_v010.py`.

The live audit passed. In particular it re-read the recent face-cover and circuit-step theorem IDs as **Proved**, including:

- `7815b37c-dab5-42b8-a1ed-fbb08d1eab5b`
- `27bd88d2-6943-4ca3-abbd-170264c17b98`
- `599aaead-0333-4d91-8bc5-d7e3e8b9831a`
- `76cdff62-bb43-4758-a1ed-980ce0ec5230`
- `bfea4b5b-106a-4e52-8297-b8138ca0a294`
- `bd9710b8-067a-4ce6-8ab9-1f6f763133b7`

The actual formal frontier child

`Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`

(theorem `73beca40-31bc-42d5-8350-5ec9ac28bd3e`) re-read exactly **Open** at the same Mathlib revision. Thus the latest publications added reusable Proved structural results without changing or silently resolving the Polynomial-Hirsch dependency frontier.
