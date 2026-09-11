# Tight-row certificates for overlapping circuit-step swaps

Date: 2026-09-10 (America/New_York). Continuation of draft PR #64.
Initial baseline: `ae17119009aca095114c3f984010d368aace5708`.
Initial extension: `70f065f72cbe00a2ddb944d663f8125757a386ac`.

## Current verification and concurrent integration

While this continuation was in progress, a parallel verification effort
compiled and audited the ORIGINAL 28-declaration checkpoint package, repaired
one inner-product normalization line, and integrated it into main via PR #70
at `6a3de152ad50a79016d5b3b8a2e1803bcc1bf246`. Its receipt is
`research/CircuitCheckpointVerificationReceipt.md`; source run `34550443602`,
job `103112037411`, artifact `10180667590`.

The current #64 continuation incorporates that main commit as a merge parent,
keeps all main files, preserves the verified normalization repair in
`PolynomialCircuitStepCommutation.lean`, and adds the two blocker lemmas
without changing the already verified declarations. The original integration
note `CircuitCheckpointLocalizationContinuation.md` is a HISTORICAL account
of the earlier uncompiled baseline; its verification status is superseded by
the #70 receipt for those original declarations.

**Only the TWO newly added blocker declarations remain uncompiled in this
extension.** The combined 30-declaration gate has not passed. The original 28
are verified at #70's snapshot, not by the new finite swap tests. No new
Prove2Me verdict is claimed for this extension. No hosted run or platform
operation was launched by this continuation. The parallel verification and
publication results are not represented as local execution here.

The current formal Open leaf is
`Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`
(`73beca40-31bc-42d5-8350-5ec9ac28bd3e`); its parent is a sketch.
No new child, cyclic dependency, or Polynomial Hirsch proof is asserted.

## Result: disjoint row supports are not necessary

Let `P = {v : a_i dot v <= b_i for all i}` be a finite H-presentation and
`x -> y -> z` two maximal normalized row-circuit steps. Put

```
g = y-x,  h = z-y,  w = x+h.
```

The swap `x -> w -> z` preserves both exact displacements and maximality
**if and only if**:

1. `w` is feasible.
2. Some row `i` is tight at `w` and `a_i dot h > 0`.
3. Some row `j` is tight at `z` and `a_j dot g > 0`.

Both witnesses are required; feasibility alone is insufficient. They need
not be the same row. No boundedness, irredundancy, vertex, disjoint-support,
or sign-compatibility assumption is needed. Circuit status is preserved
because the swapped displacements are exactly `h` and `g`.

### Ordinary proof

For any feasible segment `u -> v` with nonzero displacement `q=v-u`, a row
tight at v with positive directional change certifies maximality: for t>1,

```
a_i dot (u+t*q) = b_i + (t-1)*(a_i dot q) > b_i.
```

Conversely, if no tight row has positive directional change, every increasing
row has positive slack at v. Over those finitely many rows choose a positive
epsilon smaller than the minimum of `(b_i-a_i dot v)/(a_i dot q)`. All
increasing rows remain feasible at `v+epsilon*q`; all nonincreasing rows
remain feasible as well. If there are no increasing rows, any positive
epsilon works. This contradicts maximality.

Apply the characterization to `x -> w` and `w -> z`, using `w-x=h` and
`z-w=g`. This proves the equivalence in ordinary mathematics.

The TWO new Lean candidates are
`HirschCircuit.rowCircuitStep_of_feasible_of_tight_increasing_row` and
`HirschCircuit.rowCircuitStep_swap_of_feasible_and_tight_blockers`.
They address only the sufficient direction and its helper, and have NOT
been compiled. The converse/full iff above is NOT a formalized Lean theorem.

## Strict extension with genuinely irredundant rows

In the truncated cube

```
0 <= x_1,x_2,x_3 <= 2,  x_1+x_2+x_3 <= 5,
```

the path `(0,0,0) -> (2,0,0) -> (2,2,0)` swaps through `(0,2,0)`.
Both directions change the slanted row, so their row supports overlap.
Coordinate upper bounds certify both swapped steps' maximality. All seven
rows are irredundant, checked by explicit individual violation witnesses.
The extension is therefore not merely an artifact of redundant rows.

## Executed exact tests in this continuation

`python3 scripts/test_circuit_step_blocker_swaps.py --output FILE` compares
the blocker certificate against an independent minimum-ratio endpoint test.
Every operation uses `fractions.Fraction`. Ten bounded models in dimensions
1--3 are used. Their circuits are enumerated by exact neutral kernels. Seeds
are explicit/enumerated vertices, all pair midpoints, and their barycenter.
Every feasible consecutive direction pair is tested at each seed; this is
not an all-real-points test or a universal proof.

| Classification | Two-step walks |
|---|---:|
| Successful disjoint-support swaps | 1,052 |
| Successful overlapping-support swaps | 1,304 |
| Swapped intermediate infeasible | 2,661 |
| Feasible; only first maximality fails | 364 |
| Feasible; only second maximality fails | 474 |
| Total | 5,855 |

All certificate predictions matched the independent endpoint test. The
5,195 nonvertex-start and 4,495 nonvertex-middle cases overlap the categories
above. The JSON records representative failures, the irredundant example,
and a digest of individual cases. The full new suite ran TWICE with identical
output.

- Output SHA-256: `3caf7f0d5bac6db5f1cd1aec1bbd23543c50fd09e49e4e472a0cc652fb0de85c`.
- New regression source SHA-256: `e5454c4c85b97e3c275781227587b1f54adcd370c768e706f44ffc1be9d7d44f`.
- Unchanged checkpoint suite rerun: 6,519 pairs on 25 models, output SHA-256
  `ac80905f0ae4669f3ee86a51abd8b85773287e98186a16a20284caa87b3c3126`.
  Its script was matched to Git blob `7e8300fd1a7cef92bc22c55c17d9b32889cbf91d`.
- Eight synthetic gate-control tests passed, including corrupted new hashes
  and compiler-failure rejection. These are software tests, not geometry or
  Lean verification. The fake compiler only fails; no simulated successful
  compiler or kernel-success receipt was used.
- Python AST, shell syntax, and rejection of optimized Python passed.

The older carrier-defect and ordering-obstruction suites were not rerun
LOCALLY in this continuation; their bytes/hashes are unchanged. Their later
parallel execution belongs to the #70 verification receipt, not this local
record. No local Lean/Lake executable was available and fetching the pinned
toolchain failed. The new combined source/kernel gate remains unexecuted.

## Next gate and limits

The existing #64 manual verifier now includes all four exact suites and
requires 30 fresh axiom reports: the 28 verified baseline declarations plus
the two uncompiled additions. It must actually pass before merging this
extension. All main changes are preserved; no experimental verification
workflow from #69 or #71 is imported, and no workflow trigger or pin is
modified. The original manual-only #64 workflow is retained.

```
python3 scripts/test_circuit_checkpoint_gate_controls.py
bash scripts/verify_circuit_checkpoint_continuation.sh --checks-only
bash scripts/verify_circuit_checkpoint_continuation.sh
```

Standalone public-proof compilation and any user-led publication remain
separate gates. A past baseline audit does not verify newly appended source.

This is a less restrictive exact admission test for local reorderings, not
control of their global geometric cost. The coupled-family obstruction
already allows all row-disjoint commuting moves while every order has a
large carrier. More admitted swaps do not remove that example. A global
routing argument still needs compatible portal choices or genuinely improved
geometric cost bounds. No literature-priority claim is made for this
elementary finite-H-presentation criterion.
