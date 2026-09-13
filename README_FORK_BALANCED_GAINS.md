# Overlapping coherent gain cycles

Read `research/FORK_BALANCED_GAIN_ROUTING_2026-09-13.md` and its handoff.
The new checker certifies every non-directed simple cycle as balanced using
finite fork corridors, without enumerating those cycles. Unbalanced directed
cycles may overlap; the previous isolated-cycle requirement is not imposed.

```sh
python3 scripts/test_fork_balanced_gain_cones.py
python3 scripts/fork_balanced_gain_cones.py problem.json --output result.json
```

`problem.json` has exact rational `A`, `b`, `start`, `end` fields. Do not supply
`gain_base`: no common gain lattice is required. `--certificate` expects the
inner certificate object of a prior result, not its wrapper. The reported route
is checked against all original inequalities after exact coordinate lifting.

The four prior scripts included in the standalone ZIP are unchanged dependencies;
they are not additions in the Git patch. The Lean file is an uncompiled candidate.
The general fork-recognition proof and hereditary cone/diameter application are
written out; they are not all newly formalized Lean declarations. The classical
analytic diameter theorem and the finite sampler have distinct guarantees.
