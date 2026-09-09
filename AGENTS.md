# Prove2Me cloud-agent instructions

Read `STATUS.md`, then `CLOUD_AGENT.md`, then `SKILL.md`, before doing platform work. Keep the current mission's committed Lean pin unless the target theorem reports a different `mathlib_rev`.

## Current Polynomial Hirsch handoff

`STATUS.md` is authoritative. As of 2026-09-09:

- `Hirsch.polynomial_edge_refinement_of_circuit_walks` (`099c6686-560c-48fc-b2c2-18b6a620a06e`) remains the formal Open bottleneck.
- PR #50 has two new Prove2Me-Proved geometric results: simultaneous face-preserving rounding to parent vertices and start-containment routing with nonvertex marked checkpoints.
- PR #50 also contains a verified radial fixed-final-face construction for simultaneous monotone clipping, but the complete `L + sum B_i` clipping theorem is not yet one end-to-end Lean declaration. Do not submit or describe that full theorem as Proved until the remaining breakpoint/face-cover and clipped-edge assembly is formalized.

Do not redo Santos/spindle work, circuit Child A, or already-published repair lemmas unless a defect is found. Do not create a cyclic child that depends back on an ancestor such as `balanced_polynomial_bound`.

## Authentication and network preflight

Never print, log, commit, upload as an artifact, or include in a PR an API key or bearer token. Send Prove2Me credentials only to `https://prove2.me/api/v1`.

Before claiming that authenticated Prove2Me access is unavailable, run:

```bash
python3 scripts/prove2me_auth.py check
```

This separately checks DNS resolution, the public `/health` endpoint, API-key refresh, and an authenticated `GET /environments`. It deliberately redacts credentials.

### Codex cloud

Codex **environment variables** are available during both setup and the agent phase, while Codex **secrets** are removed before the agent phase. Therefore, if this agent must refresh Prove2Me tokens or publish/verify during its run, configure `PROVE2ME_API_KEY` as an environment variable in the selected Codex environment, not merely as a setup-only Secret.

If `PROVE2ME_API_KEY` is present during the agent phase and a script expects the workspace's conventional `credentials.json`, create the gitignored file explicitly:

```bash
python3 scripts/prove2me_auth.py bootstrap --persist-api-key
```

Only run that persistence command during the **agent phase**, after setup-only secrets have been removed. `credentials.json` is gitignored and is written mode `0600`.

Agent internet access must also permit `prove2.me`. Core solver/publishing work needs `GET` and `POST`; editing explanations or metadata additionally needs `PATCH`. Keep the domain allowlist limited to what the task requires.

### GitHub Actions

GitHub repository secrets are a separate mechanism from Codex environment variables. The manual workflow `.github/workflows/prove2me-auth-smoke.yml` expects a repository secret named `PROVE2ME_API_KEY`. Run that workflow to verify that GitHub Actions can resolve Prove2Me, exchange the key, and make an authenticated API read. It performs no publication or proof submission.

## Verification claims

A successful local `lake build`, exact computational certificate, static checker, or GitHub Actions compile is evidence of local verification only. Do not describe a theorem as accepted or proved on Prove2Me until `/verify` returns the corresponding authenticated platform verdict or an authenticated read confirms `Proved` status.

For the current Hirsch workspace, the committed pin is Lean `v4.30.0` / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`. Check the target theorem's `mathlib_rev` before changing it.
