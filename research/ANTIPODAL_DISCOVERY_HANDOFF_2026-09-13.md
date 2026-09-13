# Verification handoff: complete discovery without supplied directions

Base: PR #210 at 1dd8d9b79cf31358a1a1052866f03f13a2d64398. New paths are
additions. Earlier extraction, LP, core and wall-lifting sources stay unchanged.
The standalone package includes five unchanged dependencies, including the old
test helper used solely for independent small reference geometry.

## Mathematical statement worth verifying

A compact polytope's segment factor assigns a well-defined endpoint bit to each
vertex. Any change of that bit across an ordinary edge forces its direction:
the two crossed segment endpoints are feasible, so every common tight original
row annihilates the factor vector. Strictly opposite exposed endpoints have
opposite bits for EVERY segment factor. Therefore any walk between them is a
complete finite cover of all factor directions. A monotone walk crosses each
actual factor direction exactly once.

Use the earlier exact fiber/Farkas test on EVERY covered direction. Its transverse
capacity invariance gives a greatest zonotope summand and a residual containing
no nonzero segment summand. This does not certify general Minkowski
indecomposability: the product-of-triangles control is decomposable and segment-free.

The route wrapper recognizes point/pyramid residuals using original-row equality
patterns and inherited boundedness, with the old feedback test as fallback.
It supplies an actual parent route rather than assuming one. Factor-bit changes
bound every possible original route from below; a functional annihilating all
factor directions can force one additional, disjoint step.

## Run locally before a hosted gate

```sh
python3 -m py_compile scripts/antipodal_segment_catalogue.py \
  scripts/automatic_segment_routes.py scripts/test_antipodal_catalogue.py
python3 scripts/test_antipodal_catalogue.py --stage small
python3 scripts/test_antipodal_catalogue.py --stage large
python3 scripts/test_antipodal_catalogue.py --stage negative
python3 scripts/test_antipodal_catalogue.py --stage assemble
lake build Solutions.PolynomialAntipodalSegmentCoverage
```

The 174-line Lean file has NINE axiom printouts and is UNCOMPILED. It imports
Mathlib only. It formalizes tight-row switching, scalar exposure, finite
transition coverage, and factor/extra-step lower counts. Its generic side-label
hypotheses are discharged mathematically in the note, not yet by a full formal
polytope-to-bit construction. The all-direction extraction, symbolic simplex,
point/pyramid recognition and shortest zonotope wrapper likewise remain separate
written/executable results. No new analytic normal-fan theorem is required.

Expected elaboration-sensitive points include smul_eq_zero, finite range subset,
Option/Fintype cardinality simplification and dependent Fin-index coercions.
Preserve the nonzero factor, positive segment length, strict opposite support,
common-kernel line, distinct direction and original-edge hypotheses.

## Important discovery/certificate boundaries

- Input is A,b,start,end only; the automatic entry point rejects supplied
  candidate_directions. The standalone catalogue needs only A,b,start.
- The diagnostic opposite endpoint is discovered, not assumed to equal the
  user's requested end. A valid catalogue is reusable for all requested pairs.
- Every endpoint support uses strictly positive coefficients on a tight
  full-rank basis, and the two normals are exactly opposite. Merely choosing
  two different vertices or a tied opposite face does not prove completeness.
- Coordinate Farkas bounds certify compactness of the original H-set.
- Only nonstationary original edges contribute directions. Original rank and
  endpoint blockers are independently rechecked. The symbolic pivot log is
  discovery metadata, not a trusted substitute for those edge checks.
- Verify the ENTIRE derived candidate list, including zero-capacity candidates.
  Every positive-capacity factor must be fully removed before claiming a
  segment-free residual. Partial extraction is rejected for that claim.
- The complete list can be obtained after many diagnostic pivots. No uniform
  polynomial pivot, runtime or active-basis-enumeration bound is asserted.
- Point and pyramid recognition uses inherited boundedness. All-but-one-row
  apex equalities alone would not classify an unbounded cone as a pyramid.
- The H-zonotope point-core case returns shortest paths by a matching bit-change
  lower bound. General core lifts need not be shortest; small counterexamples
  are deliberately kept. Large test pairs are shortest by an extra quotient
  separator, not by confusing the general bound with the measured route.

The 32D test already has a34-edge diagnostic path to its requested target. The
new achievement there is complete factor discovery, a reusable original-H
model, and a shortestness certificate, not an alleged speed-up over that path.
Its33 true factors are recovered among34 tested directions, with no supplied
candidates. The old two-direction recognizer did not remove the other31 factors.

No workflow, pin, credential operation, hosted verification, public theorem or
Prove2Me verdict was produced. Compile locally, audit standard logical axioms,
then use one existing hosted final gate. A failed residual recognizer leaves
the standalone complete catalogue meaningful; it does not prove a large diameter.
