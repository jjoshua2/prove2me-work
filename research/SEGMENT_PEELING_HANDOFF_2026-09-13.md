# Verification handoff: exact final-H segment recognition and routing

Base: PR #210 head3d6c15df0c1abb539c912bb7de7393b115b81344.
All new paths are additions. The only runtime dependency from earlier work is
scripts/implicit_minkowski_lift.py, unchanged at SHA256
`d73c27da8b098cf654a27a1c5f0c2e0484de9f5e00b1ba74fc5199459ecb121b`.
It is included in the standalone package, not added/replaced by the patch.
The two new Lean modules depend only on Mathlib and each other.

## Highest-value theorem, not an arithmetic adapter

`segment_equality_of_farkas` proves the entire original halfspace set equals
its computed endpoint erosion plus [0,t*g]. Positive/negative row pairs receive
exact nonnegative original-row implication certificates. An actual positive-row
minimum constructs a decomposition of EVERY feasible point.
`any_segment_summand_le_sharp_width` proves no other summand can admit a larger
segment parameter when a feasible point makes one opposing-pair bound sharp.
These are genuine geometric model-equality/maximality statements, with no
assumed diameter or supplied parent polytope.

The direction-transverse capacity invariance and order independence are proved
in the note and tested, not all formalized in a new Lean declaration. The finite
RHS commutation lemma alone must not be reported as proving maximal-capacity
invariance. The feedback-core chart/routing facts are also separate from the
new Lean certificate core.

## Local commands before any hosted gate

```sh
python3 -m py_compile scripts/exact_farkas_lp.py scripts/hpoly_segment_peeling.py \
  scripts/recognized_segment_routes.py scripts/test_segment_peeling.py
python3 scripts/test_segment_peeling.py --stage unit
python3 scripts/test_segment_peeling.py --stage small
python3 scripts/test_segment_peeling.py --stage large
python3 scripts/test_segment_peeling.py --stage negative
python3 scripts/test_segment_peeling.py --stage assemble
lake build Solutions.PolynomialSegmentFiberEquality \
  Solutions.PolynomialSegmentFarkasMaximality
```

These are NEW UNCOMPILED Lean sources, with eight axiom printouts. Audit their
transitive standard-logical closure at the repository pin. Likely elaboration
repair points are finite-minimum selection, positive division rewrite names,
linear-map finite-sum coercions and nonlinear scalar normalization. Preserve
the finite global width premise and exact model equality while making repairs.
Do not weaken the latter into nonempty erosion or a one-sided inclusion.

## Evidence that must remain distinct

- Inputs to the integrated constructor: ORIGINAL final A,b,start,end and candidate
  DIRECTIONS. No segment parameter, decomposition, coarse chart or route is supplied.
- The exact maximal capacity statement is general for compact H-polytopes in a
  specified direction. Candidate discovery is not universal or implemented here.
- A positive primal/dual certificate is checked for EVERY opposing row pair;
  a feasible sharp pair gives maximality. Sparse multipliers refer to original
  row occurrences, including redundant/constant rows.
- Redundancy deletion is sequential, with nonnegative combinations of retained
  OTHER rows. Never delete mutually redundant rows simultaneously without proof.
- A successful affine feedback chart has positive u, nonnegative F and a strict
  positive witness Fw<w. It is not an assumed cube-graph oracle. Once discovered,
  the chart is reused to route every tested endpoint pair.
- Discovery tries the projected source as an anchor; it is not complete for all
  hidden charts. A fully peeled lower-dimensional residual can be certified by
  the extractor but not recognized by the present2d-row full-dimensional router.
- The exact simplex implementation is capped and may have exponential pivot
  behavior. Polynomially many LP calls do not establish a polynomial pivot bound.
- Verification uses no LP or graph search, although it recomputes the core's
  explicit coordinate bit path and the supplied support itinerary.
- All final vertices and edges are independently checked against ORIGINAL final
  H-rows, not only against the reconstructed sum. Lifts need not be shortest.
- The32D final-H example has68 genuine facets; it is a new two-segment closed-H
  fixture, not a claim about the preceding18-direction example's final facet count.

## Tests and rejected shortcuts

The triangle has zero removable horizontal capacity even though erosion by1/4
is nonempty. This is a mandatory negative control. Four-direction peeling is
checked in all24 orders, including dimension drops to a point. Repeating one
parallel candidate has capacities1 then0.

Small final inequalities are recovered from independent full supporting-plane
enumeration BEFORE calling recognition. The testing model/decomposition is not
passed to the solver. Original graph distances and every returned edge are
independently verified. Large original graphs are not enumerated. A dense hidden
affine chart, translation and row permutation/rescaling are recovered without
a supplied transform. Full receipts bind the actual source and dependency hashes.

The general remaining target is discovering useful candidate directions or
nonsegment coarse models, not assuming that every carrier passes this recognizer.
No hosted workflow, platform child or Prove2Me acceptance was produced here.
