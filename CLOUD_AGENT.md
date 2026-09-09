# Cloud-agent workspace

This is a **personal working copy** of a Prove2Me agent workspace, not a fork
of [`prove2me/prove2me_workspace`](https://github.com/prove2me/prove2me_workspace).
Use it as the clone target for cloud agents. Upstream template updates live on
that official repo; this repo holds the active mission work, including
`Definitions/`, `Theorems/`, `Solutions/`, and substantial research branches.

## Read this first

Read [`STATUS.md`](STATUS.md) before choosing a theorem to attack. `main` is a
conservative baseline and does not contain every newest proof-development file.
The status file records the authenticated Prove2Me frontier plus the active PR
branch map.

As of 2026-09-09, the formal open bottleneck is
`Hirsch.polynomial_edge_refinement_of_circuit_walks`
(`099c6686-560c-48fc-b2c2-18b6a620a06e`). The circuit-walk child is already
Prove2Me Proved, and the newest start-containment repair theorem from PR #49 is
also Prove2Me Proved. Do not restart the old Santos axis work or assume the
September 6 unsplit prescribed-face leaf is still the current state.

## Setup

1. Clone this repository (not the upstream template).
2. Read [`STATUS.md`](STATUS.md), [`AGENTS.md`](AGENTS.md), [`SKILL.md`](SKILL.md),
   and the needed files under [`references/`](references/).
3. Keep credentials outside Git. `credentials.json` is gitignored. Its
   conventional shape is:

```json
{
  "api_key": "p2m_...",
  "access_token": "",
  "expires_at": 0,
  "version": "0.9.8"
}
```

   Exchange the API key at `POST https://prove2.me/api/v1/agent/refresh`.
   Send credentials only to `https://prove2.me/api/v1`.
4. Before doing authenticated platform work, run the redacted preflight:

```bash
python3 scripts/prove2me_auth.py check
```

   It distinguishes DNS/network failure from missing credentials and
   authentication failure. It never prints an API key or access token.
5. Lean pin files (`lean-toolchain`, `lakefile.lean`, `lake-manifest.json`) are
   committed so `lake build` matches the mission environment currently in
   use. Fetch Mathlib with `~/.elan/bin/lake exe cache get` if oleans are
   missing.

## Codex cloud credentials

Codex cloud has two different configuration types with different lifetimes:

- **Environment variables** are available for the full chat, including the
  agent phase.
- **Secrets** are available only to setup scripts and are removed before the
  agent phase.

For a Prove2Me solver that must refresh one-hour access tokens or submit/poll
proofs itself, configure `PROVE2ME_API_KEY` as a Codex **environment variable**.
Merely adding it as a Codex Secret is insufficient for agent-phase refreshes.

If an agent-phase helper expects the traditional file, and
`PROVE2ME_API_KEY` is intentionally available during the agent phase, create
it with:

```bash
python3 scripts/prove2me_auth.py bootstrap --persist-api-key
```

Do not run that persistence command from a setup script just to bypass Codex's
setup-secret isolation.

Codex agent internet access is off by default. Enable it for the selected
environment and allow `prove2.me`; core API use requires `GET` and `POST`,
while edits require `PATCH`. Keep the allowlist as narrow as possible.

## GitHub Actions credentials

GitHub Actions repository secrets are independent of Codex environment
configuration. The manual workflow
[`prove2me-auth-smoke.yml`](.github/workflows/prove2me-auth-smoke.yml) expects a
repository secret named `PROVE2ME_API_KEY`. It only tests DNS, health, token
refresh, and an authenticated read; it never publishes or submits a theorem.

## Layout

```text
Definitions/   # published / local definition modules
Theorems/      # target statements (end in `by sorry`)
Solutions/     # direct proofs and sketches
```

The active PR branches may contain additional proof modules, research notes,
publication packets, and CI workflows not yet present on `main`. Follow the
branch map in `STATUS.md` when continuing recent work.

Current Lean pin (change these only when the target theorem uses a different
environment):

- toolchain: `leanprover/lean4:v4.30.0`
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`

## Remotes (local machine)

- `origin` → `prove2me/prove2me_workspace` (template; do not push mission work
  there)
- `mine` → this repo

Local compilation and static verification are not Prove2Me verdicts; only an
authenticated platform response or authenticated status read can establish
publication or acceptance status.
