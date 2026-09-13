# Verification handoff: direct dual-wall routing and separated endpoint stars

Base: main `980681f765b7458d69aee61318dfcfcaa9e2f6af`. The three modules use only
already merged imports. No #208 source, publication packet, workflow or pin is
changed. The preceding unpushed selective-carrier package is not a dependency.

## Most useful results

1. `minkowski_adj_of_parallel_support` proves an ordinary edge of a Minkowski
   sum from finite supporting-face data. `convexHull_supportFace_eq_segment`
   reduces those supporting-face obligations to the listed summand points.
2. `DeferredClipCertificate.route_and_quadratic_sweep_budget` assembles the
   SAME selected carrier sweeps and gives `2*sum(cost)<=3*(n-d)*(H+1)`.
   The paper's coordinate-simplex recognition/count argument discharges the
   explicit per-carrier bound `2L<=h(h+1)`; it is not yet an automatic Lean
   classifier. The lemma returns an actual exact-cost edge route too.
3. `source_target_facets_disjoint` and `exists_diagonal_interval_of_mem`
   capture the general-dimension obstruction to proper-face target locking.
   Its geometric interpretation, exact d+1 diameter, and existence of generic
   simple perturbations are in the note, not newly compiled declarations.

## Local checks before a hosted gate

```sh
python3 -m py_compile scripts/minkowski_wall_sweep.py scripts/test_minkowski_wall_sweep.py
python3 scripts/test_minkowski_wall_sweep.py
python3 scripts/minkowski_wall_sweep.py fixtures/spread_24_input.json
lake build Solutions.PolynomialMinkowskiExposedEdges \
  Solutions.PolynomialDualSweepRouting \
  Solutions.PolynomialSeparatedFacetStars
```

All 13 printed declarations need the pinned standard-axiom audit. These NEW
sources are uncompiled candidates; likely repair points are convexHull_min
coercions, sum/scalar normalizations, the namespace of convex_segment, and
map_sum rewriting. Do not weaken actual exposed-face equality into mere edge
parallelism, or replace occurrence sums by sums over distinct labels.

## Exact numerical reproduction

The two scripts are standard-library only. The input defines the polytope as
a finite Minkowski sum, not as an arbitrary unseen H-polytope. Endpoint
objectives must uniquely expose summand points. Nonmaximal comparison ties
are handled by a deterministic rational perturbation. The independent
verifier recomputes all wall events and proves the ENTIRE exposed face is a
segment. It does not use graph BFS or trust claimed adjacency.

The regression separately constructs small H-graphs from all point sums and
all supporting planes. It checks 441 routes, 1,456 edge occurrences, twelve
exposed-face models and seventeen rejection controls. Large examples are not
fully enumerated. The test regenerates all fixtures and the source-hashed
receipt. Execution time is a measurement, not a performance guarantee.

## Required distinctions

- The direction-count bound is classical; cite Blanchard--De Loera--Louveaux,
  arXiv:2001.09575, Theorem 1.3. Do not announce a new classical zonotope bound.
- Pair directions cover every listed summand point, with parallel classes
  merged. Missing directions or simultaneous nonparallel crossings invalidate
  the certificate.
- The intrinsic h(h+1)/2 direction count is for positive coordinate-simplex
  sums (or a separately certified count), not every Minkowski sum or zonotope.
- A general sum's sweep need not be shortest or preserve the endpoints'
  common face. The triangle counterexample is a deliberate test. A carrier
  requires an exact model of that carrier.
- The unperturbed spread box is a zonotope with distance d+1. Its generic
  simple perturbations retain the locking obstruction, NOT necessarily that
  representation or distance formula.
- No actual H-to-Minkowski recognition algorithm is supplied. Equality with
  the user's H-model needs its own certificate. For the spread family the
  analytic interval decomposition establishes equality and the tests verify
  original-row edges independently.
- No new Prove2Me status or general Polynomial Hirsch conclusion is claimed.

After local compilation and audit, use the existing single final hosted gate.
Publication needs a separate exact statement and authenticated acceptance.
