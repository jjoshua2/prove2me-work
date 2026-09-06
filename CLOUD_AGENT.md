# Cloud-agent workspace

This is a **personal working copy** of a Prove2Me agent workspace, not a fork of [`prove2me/prove2me_workspace`](https://github.com/prove2me/prove2me_workspace). Use it as the clone target for cloud agents. Upstream template updates live on that official repo; this repo holds whatever mission is in progress (`Definitions/`, `Theorems/`, `Solutions/`).

## Setup

1. Clone this repository (not the upstream template).
2. Read [`SKILL.md`](SKILL.md) and [`references/`](references/).
3. Create `credentials.json` locally. It is gitignored. Never commit it. Shape:

```json
{
  "api_key": "p2m_...",
  "access_token": "",
  "expires_at": 0,
  "version": "0.9.7"
}
```

   Exchange the API key at `POST https://prove2.me/api/v1/agent/refresh`. Send credentials only to `https://prove2.me/api/v1`.

4. Lean pin files (`lean-toolchain`, `lakefile.lean`, `lake-manifest.json`) are committed so `lake build` matches the mission environment currently in use. Fetch Mathlib with `~/.elan/bin/lake exe cache get` if oleans are missing.

## Layout

```
Definitions/   # published / local definition modules
Theorems/      # target statements (end in `by sorry`)
Solutions/     # what you submit as `theorem solution`
```

Current Lean pin (change these if the next mission uses a different environment):

- toolchain: `leanprover/lean4:v4.30.0`
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`

## Remotes (local machine)

- `origin` → `prove2me/prove2me_workspace` (template; do not push mission work there)
- `mine` → this repo
