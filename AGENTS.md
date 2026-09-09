# Prove2Me cloud-agent instructions

Read `main/STATUS.md` (or the latest authoritative `STATUS.md` on main), then `SKILL.md`, before choosing mission work.

## PR #50 public state

Source verification: commit `7cea19e9abdd16607bbfdaf5919f4a1433b6d416`, Actions `34403714961`, 16 new declarations / 39 axiom reports, only `propext`, `Classical.choice`, `Quot.sound`.

Authenticated publication run `34406122009` independently rebuilt/audited standalone packets and produced:

- `Hirsch.face_preserving_vertex_selection` — theorem `c8ebefd3-d31a-4d33-b1f8-6298669cc3ba`, submission `5c026214-1592-4db8-bc03-be242ced7b18`, **ACCEPTED / Proved**.
- `Hirsch.face_interval_cover_route_bound_of_feasible_start_containment` — theorem `6dc401ab-6fc2-48c9-a3fa-7e1a2b17c102`, submission `6c140ee2-141f-4b4f-baa3-031a31df4f7f`, **ACCEPTED / Proved**.
- Polynomial Hirsch mission comment `dd739cf3-7749-4947-a20a-ba16a17859ef` records the radial construction and its boundary.

`Hirsch.polynomial_edge_refinement_of_circuit_walks` (`099c6686-560c-48fc-b2c2-18b6a620a06e`) remains the formal Open bottleneck.

The full radial simultaneous-clipping `L + sum B_i` theorem is **not** yet one end-to-end Lean declaration; remaining formal assembly is finite breakpoint/face-cover extraction and clipped-old-edge diameter-one routing. Do not register or describe that full theorem as Proved yet.

## Authentication

Never print, commit, log, or artifact API keys/bearer tokens. Send Prove2Me credentials only to `https://prove2.me/api/v1`.

Before claiming authenticated access is unavailable:

```bash
python3 scripts/prove2me_auth.py check
```

For Codex agent-phase publication, `PROVE2ME_API_KEY` must be available as an environment variable; setup-only Secrets disappear before the agent phase. If needed, create the gitignored conventional file during the agent phase with:

```bash
python3 scripts/prove2me_auth.py bootstrap --persist-api-key
```

GitHub Actions repository secrets are separate from Codex configuration.

## Verification claims

A local `lake build`, deterministic exact certificate, or green GitHub workflow is not a Prove2Me verdict. Claim `Proved` only after authenticated `/verify` returns `ACCEPTED` or authenticated live status says `Proved`.

Current mission pin: Lean `v4.30.0`, Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
