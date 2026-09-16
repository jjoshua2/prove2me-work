# Direct-shadow and path-union handoff

Base main: 5e811793529ebacce9731c39cfe3d1b9d082e7c2. Coordination on #267:
comment5690366602. Other agents own bounded-length SMT, the recovered Fano/
coordinate-simplex line and private-marker refinement; do not duplicate them.

Four new scripts and a written proof supply generic ORIGINAL-H shadow routing
and shortest paths in the explored union of finitely many such routes. No full
flagification, edge-direction catalogue, supplied neighbor graph or Minkowski
model. Nonsimple vertices and lower-dimensional bounded presentations work.
All original rows common to source and target stay locked.

## Quantitative statement to preserve

After positive integer row normalization, H bounds original normal entries,
G=(d-1)!H^(d-1), C=2(dHG)^2, R=2C+2. With ordered endpoint row bases,

    f=sum_i R^(d-1-i) U_i,
    h=sum_j R^(d*(d-1-j)) V_j.

Distinct ordered-pair exponents prevent coefficient collisions in every
2x2 edge-evaluation determinant. Cofactor bounds and leading-term dominance
make them nonzero simultaneously without enumerating directions. Positive
endpoint coefficients expose the specified vertices. The bit size, not the
integer magnitude or numerical condition, is polynomial.

A complete L-edge shadow has2L-1 primary support queries and at mostL-1
additional tie-resolution queries, plus2d original boundedness calls. Earlier
coordination said2L-1 without yet counting the tie solve: do not repeat that
as a bound on ALL calls. The unchanged shifted/free-variable LP can return an
original edge-interior point. Check original rank; if absent, optimize h on
its exact exposed equality. Do not assume every tableau optimum is an original
vertex, or use the newly added support row to fake original rank.

## Soundness and cost limits

The auditor uses explicit original-row right inverses, feasibility and endpoint
blockers; it runs no optimization/rank search. Whole support queries have exact
primal/dual certificates. Working-face edges also pass ORIGINAL edge checks.
The LP's pivot count remains separate from its support-call count.

Black2024, arXiv2403.04886v2 Theorem1.2, proves that some d-polytopes with4d
facets have endpoint pairs for which EVERY coherent path needs2^d edges.
This is not merely a bad default objective. Our complete-shadow primitive does
not evade it. Do not advertise searching for one uniformly short projection as
an open sufficient premise: that premise is false.

The union can switch between sampled shadows. Its independent 1-Lipschitz
integer distance potential proves shortestness ONLY in the discovered union.
All edges are audited original edges and common facets are retained. Discovery
still pays for the constituent lengths; a short final path does not make a
long sample free. No fixed number of shadows, full union size, or universal
Hirsch bound is proved. A useful next direction would be rigorously budgeted
useful prefixes/restarts or another direct edge source, not more full shadows
claimed cheap without evidence.

## Actual controls

Small suite:11 graphs,70 vertices/132 edges,2169 active systems;249 routes,
298 edges versus285 BFS,11 nonshortest.408 primary queries plus1 real tie
resolution;3514 whole-envelope comparisons and13700 determinant tests.
Four opposite boxes through12D give d edges and no graph enumeration.

Same cyclic family as #267, d4/6/8: default6/12/20, two sampled shadows5+5,
8+8,13+13, spliced4/6/10, true distances4/6/8. The d6 best pair was chosen
AFTER an exploratory36-rotation search, not pre-registered; that exploratory
cost is not the final two-candidate call count. The d8 adverse result is kept.
Only d4 has an independent full graph here; higher controls have explicit
independently audited d-edge paths and the separate simple-facet lower bound.
Do not claim a new cyclic diameter theorem or that the spliced path cannot
be some other untested shadow.

Eight additional small unions use18 shortest original edges.18 primitive and
9 union malformed cases fail. Audits pass with optimizer/inverse/rank and,
for the union, BFS disabled. An attempted d10 cyclic exploration exceeded a
local call budget; there is no completed d10 cyclic claim.

## Reproduce and publish discipline

    python3 scripts/test_certified_rational_shadow.py
    python3 scripts/test_certified_shadow_union.py

Dependency: exact_farkas_lp.py, Git blob ea511a79164d953792942d8be3dd3537646738d6,
unchanged. Full reports/six fixtures regenerate; hashes and clean replay are
recorded separately. Test-only SymPy is not the route algorithm's input.

This is RESEARCH/Python. There is no new Lean module, axiom audit, hosted gate
or Prove2Me submission. Do not trigger publication for these files. The current
runtime has no Lean/Lake executable; source and exact tests are not compiled
formal proofs. Keep accepted packets, workflow security and pins unchanged.
