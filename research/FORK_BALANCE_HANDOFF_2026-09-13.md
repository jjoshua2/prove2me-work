# Verification handoff: overlapping gain cycles via complete fork corridors

Base PR #210 source: `2024394ac48ad8c3220f35e60246154c2904f057`.
All paths in the incremental patch are additions. The four bundled older scripts
are unchanged dependencies and are NOT new files in the Git patch.

## Highest-value contribution

Replace isolated coherent unbalanced cycles by the intrinsic property:
**every noncoherently directed simple cycle has gain one**. The paper proves
an exact finite recognizer using all inward/outward forks, balanced block-cut
corridors in the vertex-deleted graph, and single-attachment outside components.
The completeness argument uses a two-connected-block ear construction. This
allows arbitrary overlap and exponentially many coherent unbalanced cycles.

Every nonsingular sparse basis still consists of pinned trees and unbalanced
unicyclic components. The new criterion makes each such cycle coherent, so the
old positive cycle-center argument applies to EVERY basis. It is reused on
individual bases only, then transported back to the global gauge. The whole
support graph is not falsely offered to the old isolated-cycle verifier.

A product of the d largest gauged edge distortions bounds all simple paths and
cycles. Exact equality-component lifting proves the SAME transport bound for
an actual h-dimensional endpoint face. At Gamma<=2 the classical normal-cone
theorem gives256h^3 and the existing cubic adapter givesD+768H^2(n-d).
No new copy of that adapter or external analytic axiom is added.

## Local commands

```sh
python3 -m py_compile scripts/fork_balanced_gain_cones.py \
  scripts/test_fork_balanced_gain_cones.py
python3 scripts/test_fork_balanced_gain_cones.py
lake build Solutions.PolynomialForkCorridorCertificates
```

The new142-line Lean file is UNCOMPILED, with seven axiom printouts. Compile
and fix elaboration at the repository pin, then check the transitive standard
logical axiom allowlist. Likely minor repair points are real division-cancel
lemma names and natural interval indices. Do not replace the single-attachment
condition by a path assertion: the certificate must prove all simple paths are
confined, not assume the desired route is.

The finite Lean primitives do not yet include the full Tarjan/ear-completeness
proof or the all-basis/hereditary geometry. Those have complete written arguments
and exact computational tests, not a claimed end-to-end kernel verdict. The
classical Dadush--Haehnle wide-normal-fan theorem remains external and attributed.

## Test reproduction and evidence

The test supports `--part classifier`, `basis`, `small`, `large`, `negative`,
and `assemble` for resource-limited sessions. Default runs everything. Partial
runs have named receipts; the final receipt hashes the exact source and older
dependencies. The large examples regenerate source/route/cone fixtures.

The classifier is checked against independently enumerated simple cycles in
15,756 exhaustive small gain graphs,216 parallel multigraphs and300 sampled
graphs. Actual basis cones are separately checked with Gaussian inversion.
Small original-H graphs are independently enumerated; large cases are not.

The million-cycle case has61 variables,142 rows,40 forks and120 corridor entries.
It certifies the global structural property and a feasible target basis cone
with inverse entry2^240. It does NOT contain a constructed full route. Actual
large routes are separate at dimensions13,25,37, plus independent rescaling
and a pair of noncommensurate overlapping-cycle blocks.

## Required scope

- The mathematical recognizer is exact for the all-incoherent-cycles-balanced
  property, NOT for all wide cones or all short-diameter polyhedra.
- The forest gauge is not claimed optimal for Gamma. A large computed Gamma
  is not proof that another gauge cannot improve it.
- The quotient's naive product of row distortions can overcount. Inherited
  Gamma is justified by lifting a simple quotient path through disjoint equality
  components to a simple original path; do not assert naive product monotonicity.
- Independent bases have at most one cycle PER COMPONENT even when the full
  graph has exponentially many overlapping cycles.
- The sampler's exact output-edge checks and the analytic diameter-existence
  guarantee remain distinct. No polynomial runtime for that sampler is claimed.
- Same-sign rows remain the earlier signed solver's separate scope. Dense
  arbitrary rows and noncoherent resonant cycles are not certified here.
- Duplicate positive-proportional rays are collapsed only in the normal graph;
  every original inequality and RHS is retained in routing and verification.

No hosted verification, publication, workflow change, secret use, or Prove2Me
status mutation is performed by this packet. After local green, use one existing
hosted final gate rather than Actions as an interactive compiler.
