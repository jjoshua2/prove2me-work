# Prove2Me cloud-agent instructions

Read `STATUS.md` first for the live mathematical frontier, then read
`CLOUD_AGENT.md` and `SKILL.md` before doing platform work. Keep the current
mission's committed Lean pin unless the target theorem reports a different
`mathlib_rev`.

## Current Hirsch warning

`main` is a conservative baseline; much of the newest verified work is on the
active PR branches indexed in `STATUS.md`. Do not infer the current mission
frontier from theorem files on `main` alone.

As of 2026-09-09, the formal open research bottleneck is
`Hirsch.polynomial_edge_refinement_of_circuit_walks`
(`099c6686-560c-48fc-b2c2-18b6a620a06e`). Its circuit-routing sibling
`Hirsch.cubic_circuit_walk_bound` is already Prove2Me Proved. The old
`polynomial_access_to_given_supporting_face` leaf has therefore been
productively split; do not treat it as an unsplit unique leaf or re-prove the
finished circuit-diameter side.

The latest repair-network result,
`Hirsch.face_interval_cover_route_bound_of_start_containment`
(`ae57fc5c-9c88-45e9-b717-eb8ea9fb6cfe`), was published by PR #49 and is
Prove2Me Proved. See `STATUS.md` for the exact remaining geometric gap,
known counterexamples to overstrong bridge/overlap claims, and the branch map.

## Authentication and network preflight

Never print, log, commit, upload as an artifact, or include in a PR an API key
or bearer token. Send Prove2Me credentials only to
`https://prove2.me/api/v1`.

Before claiming that authenticated Prove2Me access is unavailable, run:

```bash
python3 scripts/prove2me_auth.py check
```

This separately checks DNS resolution, the public `/health` endpoint,
API-key refresh, and an authenticated `GET /environments`. It deliberately
redacts credentials.

### Codex cloud

Codex **environment variables** are available during both setup and the agent
phase, while Codex **secrets** are removed before the agent phase. Therefore,
if this agent must refresh Prove2Me tokens or publish/verify during its run,
configure `PROVE2ME_API_KEY` as an environment variable in the selected Codex
environment, not merely as a setup-only Secret.

If `PROVE2ME_API_KEY` is present during the agent phase and a script expects
the workspace's conventional `credentials.json`, create the gitignored file
explicitly:

```bash
python3 scripts/prove2me_auth.py bootstrap --persist-api-key
```

Only run that persistence command during the **agent phase**, after setup-only
secrets have been removed. `credentials.json` is gitignored and is written
mode `0600`.

Agent internet access must also permit `prove2.me`. Core solver/publishing work
needs `GET` and `POST`; editing explanations or metadata additionally needs
`PATCH`. Keep the domain allowlist limited to what the task requires.

### GitHub Actions

GitHub repository secrets are a separate mechanism from Codex environment
variables. The manual workflow `.github/workflows/prove2me-auth-smoke.yml`
expects a repository secret named `PROVE2ME_API_KEY`. Run that workflow to
verify that GitHub Actions can resolve Prove2Me, exchange the key, and make an
authenticated API read. It performs no publication or proof submission.

## Verification claims

A successful local `lake build`, static checker, or GitHub Actions compile is
evidence of local compilation only. Do not describe a theorem as accepted or
proved on Prove2Me until `/verify` returns the corresponding authenticated
platform verdict or an authenticated read confirms live status.

For the current Hirsch workspace, the committed pin is Lean `v4.30.0` /
Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`. Check the target theorem's
`mathlib_rev` before changing it.
