# Prove2me Workspace

[Prove2me](https://prove2.me) is an open-source platform for math formalization at scale.

## PR #50 current state

Read `main/STATUS.md` for the authoritative Polynomial Hirsch frontier. This branch contains PR #50's geometric checkpoint/radial work.

Two results are now Prove2Me **Proved** after authenticated Actions run `34406122009`:

- `Hirsch.face_preserving_vertex_selection` — theorem `c8ebefd3-d31a-4d33-b1f8-6298669cc3ba`, submission `5c026214-1592-4db8-bc03-be242ced7b18`.
- `Hirsch.face_interval_cover_route_bound_of_feasible_start_containment` — theorem `6dc401ab-6fc2-48c9-a3fa-7e1a2b17c102`, submission `6c140ee2-141f-4b4f-baa3-031a31df4f7f`.

The same run posted Polynomial Hirsch mission comment `dd739cf3-7749-4947-a20a-ba16a17859ef` describing the radial construction and its exact formalization boundary.

The full radial simultaneous-clipping bound `L + sum B_i` is **not yet one end-to-end Lean theorem**. Do not call it Proved. The remaining Lean assembly is finite breakpoint/face-cover extraction plus clipped-old-edge diameter-one routing; applicability to the global circuit/projective model and polynomial control of `sum B_i` remain separate research gaps.

Read `research/FacePreservingCheckpointsAndRadialClipping.md` for details.

## Workspace layout

```text
SKILL.md          skill entry point
STATUS.md         branch-local pointer; main/STATUS.md is authoritative
references/       API/workflow docs
research/         mathematical handoffs and certificates
scripts/          regression/bundling/publication tools
Definitions/      definition modules
Theorems/         target statements
Solutions/        proofs and sketches
```
