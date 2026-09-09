# Prove2Me cloud-agent instructions

Read `STATUS.md`, then `CLOUD_AGENT.md`, then `SKILL.md`, before doing platform work. Keep the current mission's committed Lean pin unless the target theorem reports a different `mathlib_rev`.

## Current Polynomial Hirsch handoff

`STATUS.md` is authoritative. As of 2026-09-09:

- `Hirsch.polynomial_edge_refinement_of_circuit_walks` (`099c6686-560c-48fc-b2c2-18b6a620a06e`) remains the formal Open bottleneck.
- PR #50 has two new Prove2Me-Proved results: `Hirsch.face_preserving_vertex_selection` (`c8ebefd3-d31a-4d33-b1f8-6298669cc3ba`) and `Hirsch.face_interval_cover_route_bound_of_feasible_start_containment` (`6dc401ab-6fc2-48c9-a3fa-7e1a2b17c102`).
- PR #50's radial simultaneous-clipping `L + sum B_i` construction is not yet one end-to-end Lean theorem. Do not submit or describe the full clipping theorem as Proved until finite breakpoint/face-cover extraction and clipped-old-edge diameter-one assembly are formalized.

Do not redo Santos/spindle work, circuit Child A, or already-published repair lemmas unless a defect is found. Do not create a cyclic child depending back on an ancestor such as `balanced_polynomial_bound`.

## Authentication and network preflight

Never print, log, commit, upload as an artifact, or include in a PR an API key or bearer token. Send Prove2Me credentials only to `https://prove2.me/api/v1`.

Before claiming authenticated Prove2Me access is unavailable, run:

```bash
python3 scripts/prove2me_auth.py check
```

This separately checks DNS, public health, API-key refresh, and an authenticated environment read while redacting credentials.

### Codex cloud

Codex environment variables persist through the agent phase; setup-only Secrets do not. If the agent must refresh tokens or publish/verify during its run, configure `PROVE2ME_API_KEY` as an environment variable in the selected Codex environment.

If a helper expects the conventional gitignored file, create it during the agent phase with:

```bash
python3 scripts/prove2me_auth.py bootstrap --persist-api-key
```

Agent internet must permit `prove2.me`; normal solver/publication work needs `GET` and `POST`, while edits additionally need `PATCH`.

### GitHub Actions

GitHub repository secrets are separate from Codex configuration. `.github/workflows/prove2me-auth-smoke.yml` expects repository secret `PROVE2ME_API_KEY` and performs only a redacted connectivity/auth read.

## Verification claims

A local `lake build`, exact computational certificate, static checker, or GitHub Actions compile is not a Prove2Me verdict. Describe a theorem as accepted/Proved only after authenticated `/verify` returns `ACCEPTED` or an authenticated read confirms `Proved`.

Current Hirsch pin: Lean `v4.30.0` / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
