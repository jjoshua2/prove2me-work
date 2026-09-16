# Continue from direct fixed-budget original-edge search

Read live STATUS, exact main SHA and active PR heads first. This is research
software and a written equivalence, NOT a Lean or Prove2Me theorem. Prior #267's
complete-refinement obstruction is unchanged. #264 and #244/#238/#250 remain
separately owned. No accepted/pending theorem is resubmitted.

Production input is rational A,b,start,target plus L. It has NO graph, refinement,
nonface catalogue, objective or nonrevisiting requirement. Nonsimple vertices,
redundant inequalities, unbounded polyhedra and lower-dimensional H-presentations
are supported when the endpoints are genuine vertices. Do not describe every
overdetermined active set as geometrically nonsimple: duplicates also cause that.

The default exact encoding selects d tight independent rows for each vertex and
d-1 tight independent COMMON rows per edge. Rational right inverses prove rank.
The selectors guard fixed-coefficient equalities, so the formula has no products
of unknowns: O((L+1)md^2) scalar constraints, O((L+1)md^3) dense coefficient
occurrences. It is polynomial in explicit L, not logarithmic in a huge budget.
This is a sound/complete fixed-budget equivalence, not a proof that a polynomial
L works on all polytopes and not a claim of novel bounded-model checking.

The optional lazy mode omits inverse variables initially, then learns exact
original-row dependence exclusions. A count-only candidate can be false: the
4x4 Birkhoff diagonal has8 common tight rows but rank7 in dimension9. Both final
modes reject budget1 and return budget2, independently checked on the24-vertex
permutation graph. The default inverse mode needs no geometric rank oracle in
its search. Lazy mode is complete uncapped but can learn exponentially many cuts.

Positive certificates contain ONLY rational vertices, selected rows and right
inverses. Their consumer uses no solver, elimination, or producer. A common
rank(d-1) supporting slice containing distinct original vertices is exactly
their edge. This applies beyond simple/full-dimensional polytopes. Stationary
padding is removed before output. Solver UNSAT is NOT accompanied by a separately
checked proof trace. UNKNOWN, timeout, encoding cap and rank-round cap must never
be presented as absence of a route. Full exported SMT text is hash-bound.

Actual suite:44 small endpoint pairs in two modes; each completes44 shortest
routes and44 negative one-shorter solver queries. Independent references give
65 vertices/133 edges and358 active-square systems plus the explicit4D cross
polytope. Extra Birkhoff4 and Klee--Walkup controls are separate. The unbounded
Klee--Walkup4D/8-facet input has15 vertices/24 edges and shortest distance5; the
found path has one facet reentry, which every shortest path requires. It is a
KNOWN UNBOUNDED example, not a bounded Hirsch counterexample. Adding the explicit
cap sum x<=19 gives a distinct bounded9-facet control,27 vertices/54 edges and
distance5. All original facet anchors and70/126 active-basis systems are checked.
Primary paper and exact matrix are in the note. Do not swap its >= signs.

Stress: cube5/8 exact-inverse and cube12/16 lazy routes have5/8/12/16 original
edges, shortest by original source-facet count; no full graphs. Birkhoff5 in
dimension16 has a certified shortest2-edge route, with independent common-rank
nonadjacency. On #267 cyclic inputs d6 succeeds; d8 and d16 actually time out
at two seconds, despite known short routes. This is a retained adverse result,
not a universal performance claim or a false lower bound.

110 positive routes,94 solver-UNSAT queries and2 actual timeout queries are
saved. The positive consumer replays all110 with solver, elimination, inverse
production and searches disabled. Eleven forged/invalid cases fail; four
resource-limit controls stay UNKNOWN. Dense affine/positive row scaling checks
preserve shortest distance, not an identical chosen route. Interval, stationary
and embedded-segment cases are included.

Dependencies: installed Z3 shared library via ctypes for search, standard-library
Fraction for verification; SymPy only for independent TEST references. HIRSCH_Z3_LIBRARY
can select the library. No internet, credentials, package installation or binary
library is included. Actual version and report/source hashes are recorded.

    python3 scripts/test_original_route_bmc.py
    python3 scripts/original_route_bmc.py input.json --budget 8 --output result.json
    python3 scripts/original_route_bmc.py input.json --budget 8 --method lazy --output result.json

Pass only result['certificate'] to --verify. Full outputs regenerate; large
formula/certificate fixtures are bundled rather than committed. Search may
remain exponential. The new tool supplies unrestricted positive witnesses for
research and formalization, not the universal polynomial diameter bound. Do not
publish an open child that merely asserts the missing bounded-budget existence.

The repository stores ORIGINAL_ROUTE_BMC_SUMMARY.json as a derived summary and
ORIGINAL_ROUTE_BMC_REPLAY.json with exact raw-report hashes. The full
ORIGINAL_ROUTE_BMC_TESTS.json and solver fixture are in the bundle and regenerate
from the tests; they are not silently claimed committed.
