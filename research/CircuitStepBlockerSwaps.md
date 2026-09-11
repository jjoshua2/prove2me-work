# Tight-row certificates for overlapping circuit-step swaps

Date: 2026-09-10 (America/New_York). Continuation of draft PR #64.
Baseline: `ae17119009aca095114c3f984010d368aace5708`.

## Evidence boundary

This note contains an ordinary mathematical proof and executed exact finite
regressions. The two added Lean declarations are **candidates, NOT compiled**.
They do not have a Lean kernel or Prove2Me verdict. Existing unverified
checkpoint/carrier sources are not promoted by these tests. No new PR, hosted
workflow, platform submission, credential operation, or merge is required by
this continuation.

The current formal Open frontier, per `main/STATUS.md`, is
`Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`
(`73beca40-31bc-42d5-8350-5ec9ac28bd3e`). Its parent is a sketch. This
continuation does not change that graph or claim Polynomial Hirsch.

## Result: disjoint row supports are not necessary

Let `P = {v : a_i dot v <= b_i for all i}` be a finite H-presentation, and let
`x -> y -> z` be two maximal normalized row-circuit steps. Write

```
g = y-x,  h = z-y,  w = x+h.
```

The swap `x -> w -> z` preserves the exact two displacements and their
maximality **if and only if** these three finite conditions hold:

1. `w` is feasible.
2. Some row `i` is tight at `w` and `a_i dot h > 0`.
3. Some row `j` is tight at `z` and `a_j dot g > 0`.

The two witness rows need not be the same, and their existence is not implied
by feasibility alone. No boundedness, irredundancy, vertex, disjoint-support,
or sign-compatibility assumption is needed. Circuit status is preserved
because the swapped displacements are exactly `h` and `g`, not rescaled
approximations.

### Ordinary proof

First consider any feasible segment `u -> v` with nonzero displacement
`q=v-u`, normalized to length one. A row tight at `v` with `a_i dot q > 0`
certifies maximality: for every `t>1`,

```
a_i dot (u+t*q) = b_i + (t-1)*(a_i dot q) > b_i.
```

Conversely, suppose no tight row at `v` has positive directional change.
Every increasing row then has strictly positive slack at `v`. If there are
any increasing rows, choose a positive epsilon smaller than the minimum of
`(b_i-a_i dot v)/(a_i dot q)` over those finitely many rows. The point
`v+epsilon*q` satisfies every increasing row; all nonincreasing rows remain
feasible as well. If there are no increasing rows, every positive epsilon
works. Either case contradicts maximality. This proves the tight-row
characterization for finite presentations.

Apply it once to `x -> w` and once to `w -> z`, noting
`w-x=h` and `z-w=g`. Together with feasibility and the original circuit
hypotheses, this proves the stated equivalence.

The new Lean candidates formalize the **sufficient direction** and its
single-step blocker lemma only. The converse above is ordinary mathematics,
not an additional Lean theorem. Do not describe the full iff as formalized.

## Strict extension with genuinely irredundant rows

Use the three-dimensional truncated cube

```
0 <= x_1,x_2,x_3 <= 2,  x_1+x_2+x_3 <= 5.
```

All seven rows are irredundant, checked with explicit individual violation
witnesses. The two steps

```
(0,0,0) -> (2,0,0) -> (2,2,0)
```

can be swapped through `(0,2,0)`. Both displacements change the slanted row,
so their row supports overlap. The coordinate upper bounds certify
maximality after the swap. The slanted row stays feasible but is not tight
on this square. Thus the extension is not an artifact of adding redundant
rows to a product box.

## Executed exact tests

`python3 scripts/test_circuit_step_blocker_swaps.py --output FILE` compares the
blocker conditions against an independently computed exact minimum-ratio
maximal-step endpoint. All arithmetic uses `fractions.Fraction`.

The deterministic test enumerates the circuit directions of ten explicitly
bounded models in dimensions 1--3. Seeds are their enumerated or explicit
vertices, every pair midpoint, and the vertex barycenter. For each seed it
checks all feasible consecutive pairs of those circuit directions. This is
not an all-real-points test and not a universal proof.

| Classification | Number of two-step walks |
|---|---:|
| Successful swaps with disjoint row supports | 1,052 |
| Successful swaps with overlapping row supports | 1,304 |
| Swapped intermediate point infeasible | 2,661 |
| Swapped point feasible; only first maximality fails | 364 |
| Swapped point feasible; only second maximality fails | 474 |
| Total | 5,855 |

There were 5,195 walks starting at nonvertices and 4,495 with a nonvertex
original intermediate point; these categories overlap the classifications
above. Every proposed certificate agreed with the independent ratio test.
The JSON stores a representative of each observed classification, the
explicit irredundant example, and a digest of all individual tested cases.
The complete new regression ran **twice**, producing byte-identical output.

- New output SHA-256: `3caf7f0d5bac6db5f1cd1aec1bbd23543c50fd09e49e4e472a0cc652fb0de85c`.
- New regression source SHA-256: `e5454c4c85b97e3c275781227587b1f54adcd370c768e706f44ffc1be9d7d44f`.
- The unchanged checkpoint regression was rerun: 6,519 point pairs on 25 models;
  its output again matched `ac80905f0ae4669f3ee86a51abd8b85773287e98186a16a20284caa87b3c3126`.
- The checkpoint script was confirmed byte-for-byte against repository Git
  blob `7e8300fd1a7cef92bc22c55c17d9b32889cbf91d` before execution.
- Eight gate control-flow tests passed, including corruption of the new
  regression hash and compiler-failure rejection. These use explicitly
  synthetic fixtures; they are not mathematical or Lean verification.
- Python AST parsing, shell syntax, and refusal to run the new exact suite
  with assertions disabled passed.

The older carrier-defect and ordering-obstruction suites were **not rerun**
in this continuation. Their source and expected hashes are unchanged. The
complete combined source/kernel gate was **not run**: no Lean/Lake executable
is installed in this session, and fetching the pinned toolchain failed.
No synthetic successful compiler output or kernel-success receipt was used.

## Integration and next gate

The same PR #64 is extended in place. The existing manual gate now includes
the new exact suite and requires **30** fresh axiom reports (the former 28
plus the two blocker declarations). No workflow trigger, Lean pin, Mathlib
pin, or previously checked theorem source is changed.

```
python3 scripts/test_circuit_step_blocker_swaps.py
python3 scripts/test_circuit_checkpoint_gate_controls.py
bash scripts/verify_circuit_checkpoint_continuation.sh --checks-only
bash scripts/verify_circuit_checkpoint_continuation.sh
```

The last two commands remain the combined gates to execute in a pinned local
Lean workspace; passing the first two does not stand in for them. Keep the PR
draft until the source compilation and the fresh 30-declaration axiom audit
actually pass. Standalone public proof compilation and any later user-led
publication are separate gates.

## What this does and does not advance

The result gives a less restrictive, exact admission test for candidate local
reorderings. It distinguishes infeasibility from failure to preserve each
step's maximality. Evaluating its row conditions does not require vertex or
face enumeration.

It does **not** prove that reordering achieves small carrier dimensions or
polynomial total repair cost. The existing coupled-family obstruction in
`test_circuit_ordering_obstruction.py` already has pairwise row-disjoint
commuting directions while every order has a large carrier. Admitting more
swaps cannot remove that example. A useful global routing theorem still
needs control of compatible portal choices or a genuinely smaller geometric
cost, not just a more permissive swap rule. No literature-priority claim is
made for this elementary finite-H-presentation certificate.
