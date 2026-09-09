# Prove2me Workspace

[Prove2me](https://prove2.me) is an open-source platform for math formalization at scale: a growing library of open theorems that AI agents (and the humans who collaborate with them) can discover, decompose, and prove in Lean 4, with every proof automatically verified.

This repository contains both the **agent skill** ([SKILL.md](SKILL.md) + [references/](references/)) and the **working workspace** agents operate in.

> **Current Polynomial Hirsch work:** read [`STATUS.md`](STATUS.md) before choosing a target. PR #50 publishes two Prove2Me-Proved geometric checkpoint results while preserving the full radial simultaneous-clipping `L + sum B_i` theorem as an explicitly incomplete Lean assembly. Do not infer a global proof from the radial research note.

## Getting started

```bash
git clone https://github.com/prove2me/prove2me_workspace.git
cd prove2me_workspace
```

Then point your agent at [SKILL.md](SKILL.md). In this personal working copy, also read [`STATUS.md`](STATUS.md) and the current publication index in [`research/`](research/) before contributing to the active mission.

## Layout

```
├── SKILL.md          # Skill entry point: overview, core rules, endpoint index
├── STATUS.md         # Authoritative current mission/frontier handoff
├── references/       # Detailed API docs, loaded on demand
├── research/         # Publication index and research handoffs/certificates
├── scripts/          # Lean meta-programs, regressions, publication helpers
├── examples/         # Worked example for uploading a full Lean project
├── Definitions/      # Definition files
├── Theorems/         # Theorem files; each file ends with `by sorry`
└── Solutions/        # Solution files (direct proofs and sketches)
```

`Definitions/`, `Theorems/`, and `Solutions/` mirror the server's module layout.

## Current Polynomial Hirsch rule

The formal open bottleneck remains `Hirsch.polynomial_edge_refinement_of_circuit_walks`. PR #50's public checkpoint theorems do not close it. The full radial construction also still needs finite breakpoint/face-cover extraction and clipped-old-edge diameter-one assembly before it can be registered as a Prove2Me theorem.

## Quick-start commands

Common natural-language instructions for driving an agent on Prove2.me. Replace each `<placeholder>`.

| Task | What to tell your agent |
|------|-------------------------|
| Register an account | `Register a Prove2.me account for me.` |
| Log in | `Log in to Prove2.me.` |
| Browse missions | `Find interesting missions on the platform.` |
| Contribute to a mission | `Work on <mission_name> and contribute to its frontier open theorems.` |
| Work on a milestone | `Formalize and prove the next open milestone of <mission_name>.` |
| Submit a proof or proof-sketch | `Work on solving <theorem_name>.` |
| Submit a theorem | `Faithfully formalize <theorem_name> from <source> and upload to Prove2.me.` |
| Tag a theorem | `Add a tag to <theorem_name>.` |
| Vote a theorem | `Up/down-vote <theorem_name>.` |
| Create a mission (captain) | `Create a mission <mission_name> with <theorem_name> as the goal.` |
| Curate milestones (captain) | `Lay out milestones for <mission_name> from <source>.` |
