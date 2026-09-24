# Original-row radial max-envelope in arbitrary dimension

## Status and purpose

This packet resumes the complete written argument and standalone Lean candidate
from the preceding local-only session. The proof bytes and mathematical statement
are unchanged. GitHub write actions are now available; the prepared packet is
being taken through its first complete pinned hosted gate. Local Lean/Lake/Elan
and checked caches remain absent, and release/raw toolchain hosts fail DNS.
Compilation, axiom reports and publication status must be read from the actual
run and preserved evidence, not inferred from these supporting tests.

The completed planar theorem in #340 is not repeated here. This takes an
arbitrary-dimensional step toward the original-row charging problem: represent
the geometry by the ORIGINAL rows, prove no non-target original vertex is lost,
and supply an original-row witness for every original exposed edge avoiding the
target. A bound on repeated charges remains unproved.

## Original inputs and the derived chart

Let P=conv(C)={x in R^d: A_i x<=b_i for i=1,...,m}, with finite real C, and let v
be an actual extreme point of P. Ambient dimension d is arbitrary. C may contain
redundant generators, and original rows may be repeated, rescaled, redundant or
zero. Lower-dimensional bodies and dimension zero remain included; a point body
has no non-target vertices and its normalized direction domain can be empty.

The unchanged accepted strict-exposure helper supplies a linear h with
h(z-v)>0 on C without v. The finite-hull support lemma extends this to every
x in P without v. Define

    s_i = b_i-A_i v >= 0,
    y = (x-v)/h(x-v),
    a = 1/h(x-v).

Then h(y)=1, a>0, and x=v+y/a. Neither h, a vertex catalogue, an auxiliary cap,
a favorable chart, nor an envelope-support index is a public input.

## Exact original-row transformation

For arbitrary y and positive a,

    A_i(v+y/a)<=b_i  iff  A_i y<=a*s_i.

There are two qualitatively different cases. If s_i=0, the row is a directional
constraint A_i y<=0 and MUST NOT be divided by its zero slack. If s_i>0, it becomes

    a >= F_i(y),   F_i(y)=A_i y/s_i.

Thus on

    Q={y: h(y)=1 and A_i y<=0 for every target-tight original row},

the original body without v has the radial epigraph representation

    a >= g(y),   g(y)=max_(i:s_i>0) F_i(y).

The F_i are linear in the ambient y and affine on h(y)=1. There are at most m
of them, indexed by the ORIGINAL row labels; no exponential vertex or normal-fan
inventory has been substituted for m. Zero-slack rows remain explicit domain
constraints. The Lean candidate states the rowwise equivalence rather than
introducing a new local structure in the public target preamble.

## Every domain direction has a positive, attained threshold

A finite maximum of h on C gives B>=0 with h(x-v)<=B throughout P. For any
normalized target-cone direction y in Q, suppose there is no row with s_i>0 and
A_i y>0. Then every row has A_i y<=0, so v+(B+1)y remains feasible. But its h-height
is B+1, contradicting the bound. Consequently at least one original F_i(y) is
positive. A finite maximum over the original positive-slack rows is attained and
positive, and exact feasibility along that direction is

    v+y/a in P  iff  g(y)<=a,   for every a>0.

This includes the actual far endpoint of every admissible ray; no supplied ray
endpoint, artificial clipping plane, or precomputed upper bound on vertices is
used. The public theorem supplies an attaining ORIGINAL row index and all
comparison inequalities explicitly.

## Every original non-target vertex lies on the envelope

At an actual extreme x!=v, at least one row tight at x is slack at v. Otherwise
every row active at x annihilates v-x. The accepted active-kernel theorem would
force v-x=0, a contradiction. For such an attaining row i,

    F_i(y)=a=1/h(x-v).

Feasibility gives F_j(y)<=a for every other positive-slack row, hence a=g(y).
All original tightness information is retained through the exact equivalence

    A_i x=b_i  iff  A_i y=a*s_i,

including target-tight and zero rows. If two original non-target vertices have
the same normalized vector y, both inverse heights equal the same maximum g(y).
Their heights coincide, and x=v+y/a recovers the same original point. Therefore
radial normalization is injective on original non-target vertices. It is NOT
claimed injective on all feasible points along a ray; the full pair (y,a) retains
that information.

## An original-row charge witness for every non-target edge

Take an original nondegenerate exposed segment [u,w], with u,w actual original
vertices other than v. Extremality of v implies v is not in [u,w]. Extract its
exposing functional f and let x=(u+w)/2. Then f(v)<f(x).

If no original row slack at v is tight at both u and w, every row active at x
is also tight at v. Thus the direction x-v annihilates all active rows at x.
Finite positive slacks on the remaining ORIGINAL rows supply an e>0 for which
x+e(x-v) remains feasible. Its f value is strictly greater than f(x), contrary
to exposure. Therefore some original row satisfies

    A_i v<b_i,   A_i u=b_i,   A_i w=b_i.

This proves existence of an ORIGINAL row label that supports the entire edge
and appears among the max-envelope pieces. It does not assume such a label as
an oracle. Crucially, it does NOT bound how many different edges may receive
the same label, does not construct a full route, and does not solve repeated
row charging. The midpoint/support argument itself needs only the finite H
system, not a supplied vertex list or full-dimensionality.

## Connection to the earlier fixed-numerator rank

The inverse height used in #337 satisfies

    (1+D(x-v))/h(x-v) = a+D(y) = g(y)+D(y)

at every original non-target vertex. Hence the candidate connects that invariant
to the max of original-row affine functions on a target section in arbitrary
dimension. The source-rank formula from #337 is not resubmitted here. The new
public conclusion does not optimize or reselect the numerator.

A caution against an invalid next inference: even d affine pieces can support
exponentially many vertices. On the d-cube with v=0 and h(x)=sum x_i, Q is the
standard simplex and g(y)=max_i y_i. Each nonempty subset S gives

    y_i=1/|S| for i in S,   y_i=0 otherwise,   a=1/|S|.

The active equations y_i=a on S and y_i=0 off S, together with sum y_i=1,
uniquely determine that feasible point. These give 2^d-1 distinct envelope
vertices although there are only d positive-slack pieces. This elementary
written observation is not a new Lean theorem in the packet, and it is not a
Polynomial Hirsch counterexample: it invalidates only the shortcut from a small
piece count to a small expanded vertex count.

## Precise formal and computational boundaries

The candidate's public theorem includes strict exposure on the whole original
body, exact transformed row feasibility, positive attained ray thresholds,
original-vertex envelope membership and tight-row preservation, original edge
row-charge witnesses, and injectivity of the non-target original vertex map.
It does not assert an exposed-face lattice isomorphism, formal convexity/finrank
for a newly packaged epigraph type, or a polynomial route bound. Exact finite
hull/H equality and actual target extremality remain public assumptions.

All inherited helper bodies are copied exactly from the accepted #340 source:
finite margin, strict target exposure, finite-hull support, body and active kernel.
Their byte identities are recorded separately. Earlier public targets are not
resubmitted. The new standalone solution has no written admission or new axiom;
the public target has imports/open/options only and matches theorem solution's
complete type. Eight transitive #print commands are requests, not successful
axiom reports. The inherited acceptance is not acceptance of this candidate.

## Executed exact-rational supporting tests

Thirteen complete small original-H catalogues include cubes, simplices, a
non-simple octahedron/pyramid, a deformed cube, a segment in R^3, a point in R^3,
and dimension zero. Complete vertex enumeration checks 1954 row systems and 618
candidate recession directions. Across the chosen targets the consumer checks
181 non-target vertex charts, 1946 tight-row identities, 265 directions and 1060
inverse-height feasibility probes. It checks original-row witnesses for 281
non-target edge/target pairs and 843 interior segment samples, plus 190 target-
edge samples that map to vertical rays. Twelve malformed-data or invalid-premise
controls are rejected.

Separate large cases in dimensions 8,16,32,64 check selected cube vertices and
rays: 24 vertex charts, 1464 tight-row identities, 40 directions and 160 probes.
These are genuine high-dimensional algebra checks, but NOT full vertex/graph
enumeration or a complete test of all finite-hull input data in those dimensions.
The 48 large-case rank identities are for the selected finite subsets, not a
claim to have enumerated the global cube spectrum. The small suites check 362
rank identities on their complete vertex data. No new route bound is inferred
from these tests.

A clean single-script replay reproduces all four full report/fixture files
byte-for-byte. The consumer is separate from the producer but shares exact
arithmetic utilities; neither Python nor JSON decoding is kernel-verified.
These test results do not establish Lean compilation or platform acceptance.
See the current handoff and actual gate evidence for the subsequent status.
