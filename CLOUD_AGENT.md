# Cloud-agent workspace

This is a **personal working copy** of a Prove2Me agent workspace, not a fork of [`prove2me/prove2me_workspace`](https://github.com/prove2me/prove2me_workspace). Use it as the clone target for cloud agents. Upstream template updates live on that official repo; this repo holds whatever mission is in progress (`Definitions/`, `Theorems/`, `Solutions/`).

## Read current mission state first

Before choosing work, read [`STATUS.md`](STATUS.md) and the current publication index under [`research/`](research/). Do not infer the live frontier from theorem files on `main`, old PR bodies, or commit timestamps.

For the current Polynomial Hirsch mission, use the exact live leaf, publication receipts, and next theorem in `STATUS.md`. The inventory under `research/HIRSCH_UNCONNECTED_RESULTS_2026-09-12.md` includes published results outside the root graph. Do not revive the old PR #50 assembly handoff.

## Setup

1. Clone this repository (not the upstream template).
2. Read [`STATUS.md`](STATUS.md), [`AGENTS.md`](AGENTS.md), [`SKILL.md`](SKILL.md), and the needed files under [`references/`](references/).
3. Keep credentials outside Git. `credentials.json` is gitignored. Its conventional shape is:

```json
{
  "api_key": "p2m_...",
  "access_token": "",
  "expires_at": 0,
  "version": "0.9.8"
}
```

   Exchange the API key at `POST https://prove2.me/api/v1/agent/refresh`. Send credentials only to `https://prove2.me/api/v1`.
4. Before authenticated platform work, run:

```bash
python3 scripts/prove2me_auth.py check
```

   It distinguishes DNS/network failure from missing credentials and authentication failure and never prints an API key or access token.
5. Lean pin files (`lean-toolchain`, `lakefile.lean`, `lake-manifest.json`) are committed so `lake build` matches the mission environment. Fetch Mathlib with `~/.elan/bin/lake exe cache get` if oleans are missing.

## Codex cloud credentials

Codex cloud has two configuration types with different lifetimes:

- **Environment variables** are available for the full chat, including the agent phase.
- **Secrets** are setup-only and removed before the agent phase.

For a Prove2Me solver that must refresh one-hour access tokens or submit/poll proofs itself, configure `PROVE2ME_API_KEY` as a Codex **environment variable**. Merely adding it as a Codex Secret is insufficient for agent-phase refreshes.

If an agent-phase helper expects the traditional file, and `PROVE2ME_API_KEY` is intentionally available during the agent phase, create it with:

```bash
python3 scripts/prove2me_auth.py bootstrap --persist-api-key
```

Do not run that persistence command from a setup script merely to bypass Codex's setup-secret isolation.

Codex agent internet access is off by default. Enable it for the selected environment and allow `prove2.me`; core API use requires `GET` and `POST`, while edits require `PATCH`. Keep the allowlist narrow.

## GitHub Actions credentials and cost control

GitHub Actions repository secrets are independent of Codex environment configuration. The manual workflow [`prove2me-auth-smoke.yml`](.github/workflows/prove2me-auth-smoke.yml) expects a repository secret named `PROVE2ME_API_KEY`. It tests DNS, health, token refresh, and an authenticated read; it never publishes or submits a theorem.

Do **not** put `PROVE2ME_API_KEY` in ChatGPT, a chat upload, the git repo, or `credentials.json` on a PR. The key stays in GitHub Actions. After a packet is committed, `jjoshua2` (including a GitHub-connected agent posting as that user) can publish it by commenting exactly:

```text
/prove2me publish
```

on the pull request, optionally followed by packet paths. `--targets Module.Name` adds a `lake build` of that module. With `/prove2me verify` and no packet, that is a module-only compile of intermediate theorem modules; it does not publish. `/prove2me publish` still requires a packet. The durable [`prove2me-comment-publish.yml`](.github/workflows/prove2me-comment-publish.yml) workflow on `main` then:

1. resolves the PR's exact head SHA;
2. compiles and axiom-audits the standalone packet **with no Prove2Me secret**;
3. freezes the verified files as an Actions artifact;
4. runs the trusted publisher from `main` with `PROVE2ME_API_KEY`;
5. comments theorem/submission IDs and the authenticated verdict back on the PR.

`/prove2me verify` compiles packets without publishing. `/prove2me verify --targets Solutions.SomeModule` compiles that Lake module even when no packet is present. This is not a push-triggered experiment workflow. Agents must still iterate locally first; the comment is the final hosted gate.

Publication workflows must preserve the same discipline: rebuild/audit the intended proof packet, never print credentials, and record the authenticated Prove2Me verdict before updating durable status.

Hosted Actions are intentionally **not** the normal edit/compile loop. Agents must iterate with the local/cloud Lean environment first and use Actions only once a candidate is locally green or when GitHub-only secrets/publication are actually required.

For Lean jobs:

- use [`setup-lean`](.github/actions/setup-lean/action.yml) via `uses: jjoshua2/prove2me-work/.github/actions/setup-lean@main` after checkout;
- do not duplicate Elan installation or `lake exe cache get` in branch workflows;
- do not create per-attempt `push` workflows; use the shared manual/reusable [`lean-verify.yml`](.github/workflows/lean-verify.yml) or a manual-only branch workflow;
- make targeted compilation pass before running bundled standalone proofs, exhaustive regressions, axiom audits, artifact uploads, or publication;
- use `concurrency`/`cancel-in-progress` and keep exploratory artifact retention short;
- if CI exposes an ordinary Lean proof error, fix it locally rather than pushing repeated trial commits.

The default-branch [`lean-cache-warm.yml`](.github/workflows/lean-cache-warm.yml) warms the shared cache whenever the committed Lean/Mathlib environment or cache action changes. Because the cache is keyed by the pin files instead of the individual experiment/workflow name, branches using the same environment can reuse it.

## Layout

```
Definitions/   # published / local definition modules
Theorems/      # target statements (end in `by sorry`)
Solutions/     # what you submit as `theorem solution`
research/      # current mathematical handoffs, publication index, exact certificates
```

Current Lean pin (change only when the target theorem uses a different environment):

- toolchain: `leanprover/lean4:v4.30.0`
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`

## Remotes (local machine)

- `origin` → `prove2me/prove2me_workspace` (template; do not push mission work there)
- `mine` → this repo

Local compilation, exact finite checks, or a successful GitHub Actions build are not Prove2Me theorem verdicts. Only an authenticated platform response can establish publication or acceptance status. [`STATUS.md`](STATUS.md) is the authoritative human/agent handoff after those receipts are known.
