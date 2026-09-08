# Natura / Child A status — 2026-09-08

## Completed kernel proof

`Solutions/CircuitPhaseRoute.lean` now proves
`HirschCircuit.standard_cubic_circuit_bound : StandardCubicCircuitBound`
without a source-theorem assumption. Its stronger routing theorem starts at
any feasible point and ends at an extreme target, with budget `17 * n ^ 3`.
The constant is intentionally loose; optimizing it is not the current goal.

Full pinned build: Lean 4.30.0, Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

- Source commit: `f8f50b6845054cb8f051cd73f073c54e758616d9`
- Successful workflow run: `34271911632`
- Evidence artifact: `10074359939`
- Artifact SHA256: `43d19906520b87e4739606a066e75acd8358f096ed09775003027fafd627f787`
- Final axioms: `[propext, Classical.choice, Quot.sound]`
- No `sorryAx` in the full build output.
- Integrated via PR #22, after green prerequisite PRs #21, #23 and #24.

The final source interface can now instantiate
`cubic_circuit_walk_bound_of_standard` to discharge the existing Child A type.
Do not resume attempts to prove the source bound from scratch, add another
Open source-bound child, or treat this result as merely conditional.

## Proof structure and invariants

The combined finite progress set records target-zero coordinates already
zeroed and positive-target coordinates trapped below `M * v_i`, with
`M = max 2 n`. The reference is reset after either kind of progress.

A norm step is an actual maximal circuit step with `1 <= alpha <= M`; it
contracts the fixed-reference potential by `1 - 1/M` and preserves progress.
At most `4*M^2` contractions reduce the initially at-most-`M` potential to
`1/(2*M^2)`, unless arrival or a progress event occurs sooner.

Concrete elimination no longer needs a maximum-ratio selector: any positive
live target-zero coordinate q with sufficiently small `x_q/r_q` works. The
proved parameter inequalities keep all target-zero coordinates nonincreasing
and every already trapped positive coordinate between half its current value
and its trapped upper bound. The maximal-step blocker therefore creates a
strict new progress event. Each phase takes at most `4*M^2+1` steps, and the
finite-set induction permits at most n phases. Recentring and the existing
slack bridge preserve the original circuit-step relation.

This is a source-backed formalization and support-safe adaptation of Natura's
circuit-diameter result, not a claim to a new mathematical diameter theorem.

## Public platform results

Conformal decomposition into at most n elementary vectors is publicly Proved:

- Theorem `HirschCircuit.elementary_conformal_decomposition_ambient_bound`
- Theorem ID `05726681-715c-408a-b44c-d73dac856b20`
- ACCEPTED submission `9003da2a-48dd-4d30-9e64-a3f4eaf93235`
- Successful publication run `34271579650`, artifact `10074238842`.

The exact existing Child A is `Hirsch.cubic_circuit_walk_bound`, theorem ID
`9b9a6f06-d05d-41ba-980f-04b905e67562`. Its separately gated standalone/server
verification workflow is `34272583207`. At this checkpoint its platform
verdict has not yet been observed. Read the resulting `status.json` and
`proof-verdict.json` before claiming server acceptance.

## Remaining mathematical frontier

`Hirsch.polynomial_edge_refinement_of_circuit_walks` is separate. Its existing
statement allows an entirely different graph route and does not require
visiting nonvertex circuit intermediates. It still requires a polynomial
edge-walk bound; the completed circuit routing does not supply one.

Do not conflate circuits with edges or claim that Child B, the supporting-face
leaf, or the Polynomial Hirsch Conjecture has thereby been proved. Further
work should attack an actual geometric edge-routing mechanism rather than
republishing an equivalent graph-diameter hypothesis under a new name.
