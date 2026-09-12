# Prove2Me cloud-agent instructions

Read `STATUS.md`, then `CLOUD_AGENT.md`, then `SKILL.md`, before doing platform work. Keep the current mission's committed Lean pin unless the target theorem reports a different `mathlib_rev`.

## Current Polynomial Hirsch handoff

`STATUS.md` is authoritative. The synchronized 2026-09-12 frontier has one open leaf, `Hirsch.common_face_diameter_of_dim_ge_six` (`87a8b4f4-8b58-4340-8cb9-5fd1b548d01e`). Polynomial circuit-to-edge refinement remains an open ancestor. The deferred clipping/target-cone assembly and maximum-support regime are verified in merged PR #200. Integration #201 verifies exact selected-degree accounting, the selected-run excess sum, and unchanged #202 intrinsic carrier/fixed-deficit routes. Every fixed support deficit g is closed at cost D+2(g+3)2^g*r; an actual carrier has dimension h<=its excess. Merged #203 verifies positive projective graph transport and publishes the finite-certificate hidden-product n-d bound (b6289eea-78b3-4bcf-a5d7-65fbab46a986, Proved). Merged #204 records exact homogeneous chart discovery, a Proved recursive geometric-tree n-d theorem (4afd7668-51a9-4a5e-a991-2a02c53b9e1c), and locally verified D+n*r actual-pair clipping cost. Its additional contractive-feedback-box paper proof handles cyclic examples without separators, but is not yet Lean-formalized; next formalize the active-choice vertex and edge lemmas. The remaining class includes coupled carriers with no projective separator; finite failure of the detector is not a diameter lower bound. The remaining target is joint cost for coupled carriers with growing deficit. Cubes rule out forcing all shortest certificates to have logarithmic deficit. Consult STATUS.md and the #201/#202 proof notes for the exact verification and publication boundaries. Consult the public-results inventory before reproving or republishing a partial result.

Do not redo Santos/spindle work, circuit Child A, or already-published repair lemmas unless a defect is found. Do not create a cyclic child that depends back on an ancestor such as `balanced_polynomial_bound`.

## Pull-request lifecycle and backlog discipline

Open pull requests are an **active work queue, not an archive**. Branches, commits, receipts, and closed PRs preserve history; leaving completed or superseded PRs open obscures the actual frontier.

- Before opening a new PR, inspect the repository's current open PRs. Reuse or update an existing PR when it is the same active line of work instead of creating another overlapping branch.
- Every PR must end in exactly one of these states:
  1. merged into current `main`;
  2. closed as superseded/historical, with a comment naming the successor or clean integration PR when applicable; or
  3. deliberately kept as a draft, with an explicit blocker and next action in its body.
- If useful verified work sits on obsolete or heavily stacked ancestry, **do not merge the historical ancestry merely to preserve it**. Transplant the exact verified source blobs, receipts, and reproducibility material onto current `main` in a small integration PR; merge that PR; then close the historical source PR as superseded.
- Publication-only PRs and one-shot publication workflows are temporary. After the server verdict is known, preserve theorem/submission IDs and verification receipts in durable repository state, remove or exclude the one-shot workflow, and close the publication PR.
- Experimental verification workflows are not archival artifacts. Once their useful evidence is preserved in receipts/logs, delete them or exclude them from integration.
- When one PR supersedes another, close the superseded PR in the same work cycle. Do not defer routine backlog cleanup to a later agent.
- As a default for one mission, keep no more than a small handful of PRs open (roughly three) unless each additional PR has a distinct, documented active purpose.
- At handoff time, compare the open PR queue against `STATUS.md`. Every open PR should correspond to an active item named or compatible with the authoritative frontier; otherwise merge, transplant, or close it before ending the work cycle.

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

Agent internet access must also permit `prove2.me`. Core solver/publishing work needs `GET` and `POST`; editing explanations or metadata additionally needs `PATCH`. Keep the allowlist narrow.

### GitHub Actions

GitHub repository secrets are a separate mechanism from Codex environment variables. The manual workflow `.github/workflows/prove2me-auth-smoke.yml` expects a repository secret named `PROVE2ME_API_KEY`. Run that workflow to verify that GitHub Actions can resolve Prove2Me, exchange the key, and make an authenticated API read. It performs no publication or proof submission.

#### Actions cost discipline — mandatory for cloud agents

GitHub-hosted Actions are a **final verification/publication gate**, not an interactive Lean compiler or trial-and-error harness.

- Before pushing a commit that would invoke an expensive workflow, run the exact relevant Lean command locally in the cloud workspace and make it pass there first.
- During iteration, prefer `lake env lean path/to/file.lean` for one edited file and `lake build Module.Name` for the smallest affected module set. Reserve a full `lake build`, standalone packet compilation, exhaustive regression suites, and axiom/publication audits for a locally green candidate.
- **Do not create a new push-triggered workflow for each theorem, branch, proof attempt, or repair experiment.** Experimental verification must be `workflow_dispatch`/manual or reuse `.github/workflows/lean-verify.yml`. Stable long-lived `push` CI is allowed only when it is genuinely needed on `main` or another durable integration branch.
- If a GitHub verification run fails because Lean rejects the proof, fix and re-run locally. Do not repeatedly push speculative edits just to use Actions as the compiler.
- Every Lean workflow must reuse `jjoshua2/prove2me-work/.github/actions/setup-lean@main` after checkout instead of independently installing Elan/Mathlib. That action restores the shared cache keyed by `lean-toolchain` + `lake-manifest.json`, fills a miss, and saves the populated environment **before** later proof steps can fail.
- Put cheap structural/certificate checks before expensive Lean work when they can reject a bad candidate quickly; put full standalone/bundle/axiom/publication audits after the targeted source compilation succeeds.
- Use `concurrency` with `cancel-in-progress: true` for any workflow that can be superseded by a newer run.
- Do not upload proof packets/artifacts on every exploratory failure. Upload them on explicit manual/final verification or publication runs, use the narrowest paths possible, and set a short retention period unless a durable publication receipt is required.
- When the Lean/Mathlib pin changes, let `.github/workflows/lean-cache-warm.yml` populate the new default-branch cache before expensive branch verification.
- If you edit anything under `.github/workflows/`, `.github/actions/`, or the Actions policy checker, run `python3 scripts/check_actions_policy.py` locally before pushing. The policy rejects new automatic push-triggered experiment workflows.

The shared manual/reusable verifier is `.github/workflows/lean-verify.yml`. For branch-specific CI that truly needs extra audit logic, keep the branch workflow manual-only and call the shared setup action rather than duplicating dependency installation.

## Verification claims

A successful local `lake build`, exact computational certificate, static checker, or GitHub Actions compile is evidence of local verification only. Do not describe a theorem as accepted or proved on Prove2Me until `/verify` returns the corresponding authenticated platform verdict or an authenticated read confirms `Proved` status.

For the current Hirsch workspace, the committed pin is Lean `v4.30.0` / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`. Check the target theorem's `mathlib_rev` before changing it.
