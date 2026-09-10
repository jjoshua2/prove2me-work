# Natura Child A recovery + common-face composition verification

Status: verified integration receipt.

## Verified source state

- Branch: `integration/natura-child-a-recovery`
- Source commit tested: `a5756e5aeb8b2b7cc22ec94232396bb472d801eb`
- GitHub Actions run: `34530809098`
- Artifact: `10173546831` (`natura-child-a-recovery`)
- Lean: 4.30.0
- Mathlib: repository-pinned manifest/toolchain
- Build target: `Solutions.PolynomialCommonFaceCubicCircuitWalk`
- Result: build completed successfully (8519 jobs)
- Axiom audit: 5 required declarations, 108 reports checked; only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`.

Audited declarations:

1. `HirschCircuit.standardCircuitWalk_cubic`
2. `HirschCircuit.standard_cubic_circuit_bound`
3. `HirschCircuit.rowCircuitWalk_explicit_cubic_of_bounded`
4. `HirschCircuitLocalization.commonFace_edgeRefinement_ready_with_cubic_circuitWalk`
5. `HirschCircuitLocalization.rowCircuit_commonFace_ready_with_cubic_walk_excess_defect`

## Historical provenance

The constructive Natura circuit-routing source was recovered from the previously verified PR #22 lineage (`f8f50b6845054cb8f051cd73f073c54e758616d9`, `Solutions.CircuitPhaseRoute`). The recovered PR #22 route path was independently rebuilt on the current pinned environment in run `34528500332`, which succeeded and audited `standardCircuitWalk_cubic` and `standard_cubic_circuit_bound` with only the standard logical axioms.

A later historical integration snapshot also contained an obsolete alternative branch (`CircuitFiniteRouting`, `CircuitSupportSafeElimination`, `CircuitWeightedNormStep`, and `NaturaChildACandidate`). That branch was not part of the verified PR #22 route path; one obsolete module failed an arithmetic elaboration check when rebuilt. Those four files were therefore pruned before the final verification above. The final source state compiles with them physically absent.

## New mathematical composition

`rowCircuitWalk_explicit_cubic_of_bounded` transports the recovered standard-form result back through slack coordinates and proves, on a fixed bounded H-presentation, a `RowCircuitWalk` of length `17 * n^3` between any two vertices. It does not reselect rows and needs no irredundancy, strict-feasibility, or endpoint-separation assumption.

`commonFace_edgeRefinement_ready_with_cubic_circuitWalk` applies that fixed-presentation theorem to the exact common-face row model previously verified in PR #59. Thus the same selected presentation is simultaneously:

- equivalent to the full common-face coordinate H-polytope,
- bounded,
- row-irredundant,
- strictly feasible,
- equipped with both endpoint coordinates as vertices, and
- equipped with an explicit `17 * m^3` row-circuit walk between those endpoints.

For an ambient vertex-to-vertex row circuit, `rowCircuit_commonFace_ready_with_cubic_walk_excess_defect` attaches the existing excess/neutral-rank-defect inequality to that very same model. No circuit-inheritance claim after row deletion is used or needed.

## Remaining boundary

This closes the circuit-walk-existence/presentation-normalization side of the common-face route. The unresolved dynamic issue is circuit-to-edge refinement: turning the resulting row-circuit walk into an ordinary `Adj`/stay walk with polynomial overhead. The known hexagon obstruction shows that one cannot do this merely by demanding an outgoing edge direction conformal to each circuit displacement.
