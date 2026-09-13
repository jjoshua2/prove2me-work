# Verification handoff: nonsegment factors and joint scale packing

Development base: PR #210 head4b82eedf97812059490e545a8a4d02822597f87b.
Integration base: concurrent heade6f5baa858ac61e9d6c293670fe27a86b603b2dd, whose
simplex removal and local proposal code is preserved unchanged. The overlapping
simplex/Farkas mechanism was independently developed. This extension's distinct
scope is general finite point lists and the COMPLETE JOINT scale region, not a
replacement of the concurrent independent-generator simplex recognizer. All new
paths are additions; older runtime dependencies remain unchanged and hash-bound.

## The main result and its true input

For R={Ax<=b} and candidate Q=conv{0,g1,...,gk}, removal at t is equivalent to
feasibility, for EVERY x in R, of the k-variable allocation system with rows
-A_iG, -e_j, and ones. Enumerate its minimal positive dependencies, supports
at most k+1. Each restrictive circuit gives t*gamma<=beta-v*x. Exact original-H
Farkas multipliers certify the global lower capacity; one feasible sharp circuit
point proves no larger scale can occur with ANY residual.

For several candidate shapes the same construction yields ALL simultaneous
scales as a packing polytope. Minimal external circuits have nu_l=h_Ql(v), so
their scale coefficients are nonnegative support deficits. Matching original-H
primal/dual witnesses are necessary to certify the exact coefficient region,
not just a sufficient inner approximation.

Shapes ARE supplied; their scales, residuals and routes are not. This is a new
class of inputs beyond segments, not a replacement of the earlier automatic
segment catalogue with a weaker claimed complete discovery theorem.

## Local commands

```
python3 -m py_compile scripts/finite_summand_capacity.py scripts/joint_summand_region.py \
  scripts/recognized_finite_summand_routes.py scripts/test_finite_summand_capacity.py
python3 scripts/test_finite_summand_capacity.py --stage unit
python3 scripts/test_finite_summand_capacity.py --stage joint
python3 scripts/test_finite_summand_capacity.py --stage small
python3 scripts/test_finite_summand_capacity.py --stage large
python3 scripts/test_finite_summand_capacity.py --stage negative
python3 scripts/test_finite_summand_capacity.py --stage assemble
lake build Solutions.PolynomialFiniteSummandObstructions \
  Solutions.PolynomialJointExtractionGeometry
```

New Lean candidates:194lines/12printouts, Mathlib-only imports. They are uncompiled.
Audit transitive standard logical axioms. Possible API-sensitive points include
finite linear-map sums, support-bound normalization and Convex function coercions.
Do not turn a necessary allocation inequality into a falsely claimed sufficient
full Farkas theorem. The complete positive-circuit/existence bridge is written
and executable but not yet a full Lean declaration in this packet.

## Invariants that must survive repairs

- Normalize a candidate by translating its first point to zero. The capacity
  is translation-invariant; the exact reported residual uses that fixed convention.
- Affine-dependent lists are valid. Complexity uses the NUMBER of listed points,
  not the smaller geometric rank unless an additional reduction is proved.
- Every positive circuit is reconstructed in verification. A zero allocation
  normal is a singleton circuit; no larger minimal circuit may contain it.
- A cap must fail before a partial list is called complete. Fixed k is polynomial
  in original row count; unrestricted total candidate size can be exponential.
- For a single scale, global lower inequalities PLUS a sharp feasible point
  prove maximality. For a joint region, EVERY circuit RHS has a matching optimum.
- Positive original-row combinations are finite certificates, not test samples.
- Original compactness used in the point/pyramid core theorem has explicit
  dual bounds on all positive/negative coordinate directions; never omit them.
- All returned edges are checked AGAIN on original final H-rows, including rank
  d-1 common tight normals and both endpoint blockers. No circuit move is enough.
- At most v-1 true candidate support changes occur on one objective segment;
  this classical finite-vertex lift is not a new shortest-path theorem.
- Complete segment-free recognition does not imply no higher-dimensional factor.
- The joint hexagon example forbids importing segment-removal commutativity:
  triangle and square each have scale1, but the true joint region is s+t<=1.
- The linear extraction objective is not a claim about optimal residual diameter.

The 32D fixture has64 genuine facets and2,684,354,563 vertices by an explicit
base-pentagon/top-triangle proof. Its graph is not enumerated. An all-dimension
projection argument proves it segment-free; the older independent catalogue
also checks the exact supplied instances. Its four-edge sample is not asserted
shortest. The known triangular shape is supplied, not found universally.

No hosted run, platform child, credential operation or Prove2Me acceptance was
produced. After local green and standard-axiom audit use one existing hosted
gate. The residual problem remains candidate-shape discovery and broader local
routing, not a proof that every segment-free carrier has these summands.
