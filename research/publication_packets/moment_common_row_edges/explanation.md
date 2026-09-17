# Common original moment rows expose a genuine edge

## Exact target and advance

The new target is `Hirsch.moment_common_rows_expose_edges`. For any d<m and any
injective real parameters a on the m ORIGINAL labels, form the original rows

    A_i(x)=sum_(j=1..d) [a_i^j - average_(l=0..m-1) a_l^j] x_j.

Let P={x: A_i(x)<=1 for all i}. Suppose u,v are feasible and their EXACT sets
I,J of tight original inequalities each have cardinality d, with

    |I intersection J| + 1 = d.

The theorem derives that u and v are distinct actual Mathlib extreme points,
that their common feasible equality slice is EXACTLY the closed segment [u,v],
and that this entire segment is an actual Mathlib `IsExposed` and `IsExtreme`
subset of P. The exposing objective is explicit: the sum of the common ORIGINAL
rows. It is bounded above by |I intersection J| on all of P and attains that
bound exactly on the segment. Every strict convex combination of the endpoints
has exactly the common rows tight.

This is a sufficient ordinary-edge criterion, not a converse for all possible
exposed segments or a bound on how many such edges a route needs. It assumes no
vertex list, extreme-point property, row independence, rank certificate,
supporting-functional oracle, or adjacency relation. The combinatorial counts
are given on the literal original inequalities, and the missing geometric
conclusions are proved from the moment system. No projection or auxiliary
coefficient representation is used.

The cardinal hypotheses automatically exclude d=0 and equal endpoints. In d=1,
the common-row set is empty and its objective is zero. The theorem correctly
says that P itself is the whole interval between its two vertices, a genuine
one-dimensional face; Mathlib allows an exposed set to be the whole original
set. No nonzero-functional premise is silently inserted.

## Dependency reuse

The packet includes the complete namespace proof prefix of ACCEPTED #293,
`Hirsch.moment_vertex_tight_row_criterion`, byte-for-byte. Its old top-level
solution and audit suffix are removed, not resubmitted. Exact dependency:

    accepted proof: 67cba0868eb70b992baf3579e90ac800e4e3a55a
    source blob: 1b732d2f565e1b3ec767c1563079ef69bd028f05
    source SHA256: dcc127dffdbd49ba937bfd41e4cb4f52ac092c19c0f28d6b87c648b72aaa54af
    run: 35209444916
    theorem: 01977493-8c4e-45c5-957d-236e1d3fd475
    submission: 64b7b648-b7e7-4bca-a4d6-b4e95138df7a

Its verified packet was downloaded as artifact10491383552, original ZIP digest
62a9d7ab3b5e9fe9719fa0ae84af4d39ef2b10b88ae015841716a875fd2fc42c.
Every frozen file hash is checked before extracting the prefix. The accepted
Mathlib extreme-point criterion and its active-map injectivity are reused as
proved code, not restated assumptions. #293's integration is not modified,
merged or retriggered by this new packet. The other compactness, support-selection
and catalogue branches remain independent.

## Main new argument: recover the unique affine parameter

Put C=I intersection J. The cardinal difference proves I\J consists of one
row r and J\I consists of one row q. More explicitly, C=I.erase(r). No chosen
basis or enumeration of all vertices is needed.

Since r is tight at u but not at feasible v, delta=1-A_r(v)>0. At an arbitrary
feasible point z where all C rows are tight, define

    t=(1-A_r(z))/delta.

Then t>=0. The accepted source-vertex theorem makes evaluation on I injective.
Every common row has the same value at z and u+t(v-u), and the single remaining
row r has the same value by the displayed definition of t. Injectivity therefore
gives the exact vector equality

    z=u+t(v-u).

The other private row q is tight at v and strictly slack at u. Writing
eta=1-A_q(u)>0, feasibility at z gives

    A_q(z)=A_q(u)+t*eta <= 1,

so t<=1. Therefore the ENTIRE common feasible slice is contained in [u,v].
Conversely, every convex combination of the endpoints is feasible by linearity
and remains tight on C. This proves equality of sets rather than merely a line
through two points or equal objective values at two endpoints.

For a feasible z, each 1-A_i(z) is nonnegative. Their sum over C vanishes exactly
when each summand vanishes. Thus

    sum_(i in C) A_i(z) <= |C|,
    equality iff z belongs to [u,v].

The finite sum defines a linear map; finite dimensionality gives the actual
continuous linear functional used to prove Mathlib `IsExposed`. Its standard
`IsExtreme` implication supplies extremeness of this full set. The nondegenerate
closed segment with this supporting-face identity is the ordinary geometric
edge; there is no separate, unverified graph predicate renamed as adjacency.

Finally, for 0<t<1, the slack at (1-t)u+tv is a strictly positively weighted
combination of the endpoint slacks. It vanishes exactly when both endpoint
slacks vanish. This proves the exact tight-row set C on the open segment.

## Why hypotheses and whole-slice equality matter

Two feasible points can have equal objective value on a larger supporting face.
Endpoint equality alone would mistake diagonals for edges. The tests retain all
928 nonadjacent pairs in the small reference models and verify their common-row
objectives have more than those two maximizing vertices.

Injectivity of the moment parameters is also essential. In dimension3, with
parameters (0,0,1,2,3), there are feasible points

    u=(-25/3,15/2,-5/3),   v=(-15/4,5/4,0)

whose tight sets are {0,1,3} and {0,1,4}. Their counts are3 and their overlap
has2 labels, yet the common rows have rank1 and the endpoints have only rank2
active constraints. The common supporting face has three genuine vertices.
These endpoints are not extreme and their segment is not the full supporting
face. The theorem excludes this example through the actual injectivity premise;
row counts are not universally equivalent to rank on arbitrary H systems.

Feasibility is likewise separate from having d tight inequalities. The complete
small square-system reference produces286 infeasible full-tight points. Those
are not admitted as vertices by this theorem or the supporting checks.

## Tests and provenance boundaries

The exact rational suite reconstructs9 complete small moment-H models with411
independently solved square systems and125 vertices. It checks all265 adjacent
pairs against the rank-based reference and verifies their supporting objective
has exactly those two maximizing vertices. It also checks928 nonadjacent pairs,
28,816 supporting-objective vertex values,1,060 interior points and1,060 points
outside the purported segment, with21,850 original row evaluations on those
small candidate lines. No reference graph is an input to the Lean theorem.

Four further samples in dimensions8/16/32/64 use explicit root-polynomial
vertices and directly evaluate every original inequality, common row and affine
parameter identity. Their full graphs are not enumerated. Thirteen saved
consumers replay with geometric/witness production disabled. Eleven malformed
or out-of-scope controls fail, including wrong objectives, changed endpoints,
repeated parameters and Boolean/float labels. These tests are not Lean-extracted
or formal verification of Python and its JSON parser.

    python3 scripts/test_moment_common_row_edges.py

The originating runtime has no Lean/Lake executable and cannot resolve the
public toolchain host. The prepared packet therefore is not locally compiled.
The user explicitly asks for a new PR-comment proof-bundle attempt through the
existing pinned compiler/axiom gate and trusted-main publisher. Only its actual
run and authenticated receipt can establish formal verification/publication.
No workflow, pin, permission, protocol, token or secret split is changed.

The public preamble contains only import/open/settings. The formal statement is
extracted from the same top-level solution signature. There is no target import
or proof admission; five transitive axiom reports are requested. Any later
warning, error, or platform verdict must be preserved honestly.

## Remaining conjecture-level step

The packet supplies the original-edge interpretation needed by future routes
that exchange one tight moment label. It does not prove existence of a useful
exchange sequence, its connectivity or length, the cyclic domino construction,
a universal polytope diameter bound, or Polynomial Hirsch. Earlier finite
nonface/refinement obstructions and accepted compactness/catalogue results keep
their own hypotheses and scopes. A path-local upper bound remains necessary.

The finite polyhedral edge/exposed-face arguments and interpolation are classical;
no historical-priority claim is made. Mathlib's exact `IsExposed`, `IsExtreme`
and finite-dimensional continuity definitions are used under the committed pin.
Primary API references:
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Convex/Exposed.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Convex/Extreme.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/Module/FiniteDimension.html
