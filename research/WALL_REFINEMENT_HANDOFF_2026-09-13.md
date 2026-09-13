# Verification handoff: implicit-base Minkowski refinement

## Coordination

Based on PR #210 head42b16e946361ed311b4538ff4c2eb75e245b74d8. No earlier solver,
fork recognizer, proof, or publication packet is modified. The Python files are
self-contained; no previous candidate algorithm is a runtime dependency. The
Lean files import earlier Minkowski support and cubic accounting modules on
this PR; those prerequisites must be compiled before the new candidates.

## Main mathematics

Given a verified simple L-edge route in P={Ax<=b}, and added summands sum conv(Vs)
with q distinct within-summand pair-difference directions, construct an actual
route in the sum of length<=L+(L+1)q. The coarse support stays a point on each
open objective segment and is exactly the chosen parent edge at each corner.
Additional comparison-wall events or parallel corner expansions expose WHOLE
segments of the sum. This is not a circuit or an endpoint-difference test.

The separate additive theorem is B(d,tau)+5q for a tau-wide parent fan. Its proof
uses the THREE straight segments in the classical Dadush--Haehnle construction
plus two endpoint connectors. Do not infer five segments from an abstract graph
diameter bound. The current deterministic implementation proves the multiplicative
L-lift, NOT a new implementation of that analytic sampler.

An exposed octagon gives arbitrarily thin actual cones under EVERY affine
preconditioner; a second exposed star face gives exponentially many actual
directions. These can coexist with small q and the proved (q+1)d+q all-endpoint
bound. The parent has2d H-rows; do not describe those as the final sum's facet count.

## Local gates

```
python3 -m py_compile scripts/implicit_minkowski_lift.py scripts/test_implicit_minkowski_lift.py
python3 scripts/test_implicit_minkowski_lift.py --stage small
python3 scripts/test_implicit_minkowski_lift.py --stage large
python3 scripts/test_implicit_minkowski_lift.py --stage aux
python3 scripts/test_implicit_minkowski_lift.py --stage assemble
lake build Solutions.PolynomialPositiveSupportIntersections \
  Solutions.PolynomialWallRefinementBudgets
```

The225 new Lean lines have ten axiom printouts and have NOT been compiled here.
Expected elaboration-sensitive points include the linear-map finite sum/coercion,
positive weighted support equality, and existing deferred route assembly. Preserve
strictly positive supported weights, exact supporting-face equality, and occurrence
costs. Do not replace the real geometric construction by an assumed diameter.
The generic finite cores do not constitute the whole refinement-existence theorem
or a formal import of the external analytic result.

## Certificate and algorithm safeguards

- Every parent vertex is feasible against ALL original H-rows and has full
  active rank. Every parent edge has shared rank d-1 and endpoint blockers.
- Support multipliers are nonnegative, only on actually tight original rows,
  and their positive support has the required vertex/edge rank.
- Both endpoints uniquely maximize every explicit summand; changing a tied
  endpoint is not an acceptable perturbation. Exact duplicates may be removed.
- Added directions use every within-summand point pair, not an alleged edge list.
- Genericity is exact finite rational root avoidance. Parallel switches at a
  parent-edge corner are allowed but must expose a consistently oriented segment.
- Verification never calls normal discovery, graph search or support optimization
  over an implicit polytope. It reconstructs the entire exposed-face evidence.
- No graph of the final high-dimensional Minkowski sum is enumerated. Its input
  representation is P plus explicit added point lists, not an arbitrary final H-set.
- A supplied short parent route remains an input. Recognition of a useful coarse
  summand/decomposition for an arbitrary carrier is not implemented or assumed.
- Lifts need not be shortest or preserve the endpoints' smallest fine face.
  Model the actual selected carrier itself when using its local route.

## Actual evidence

The complete run checks297 routes/666 edges, with small independent base/refined
H-graphs and twenty rejected forgeries. The32D example uses18 added directions
and66 edges, with536,870,941 provable full directions and an all-affine minimum
cone-width upper bound2^-80. It is not a graph-diameter lower bound.
The executable suite stores the exact large inputs and certificates and a
hash-bound stage receipt; assembly rejects results from a different source.

After local compilation and standard transitive-axiom audit, use the existing
single final hosted gate. No new workflow, credential operation, public theorem
or Prove2Me verdict is produced by this packet.
