# Planar routes bounded by the original halfspace count, without a supplied chart

## Statement and relation to the mission

Let C be any finite set of real planar points, let A_i x <= b_i be m ORIGINAL
linear inequalities, and assume the exact whole-set identity

    conv(C) = {x in R^2 : every original inequality holds}.

For any actual extreme endpoints u,v, construct a finite sequence of original
extreme points joining them, with every step a whole nondegenerate exposed
segment of the original feasible set, and with

    2 L <= m.

Thus L <= floor(m/2). The bound uses the supplied original inequalities, NOT the
cardinality of the generator list C, an expanded vertex inventory, or an auxiliary
normalization graph. C may contain redundant boundary/interior points. Original
rows may be redundant, rescaled, repeated, or identically zero. Equal endpoints,
segments and point bodies are included. Empty bodies have no extreme endpoints.

This closes the explicit input gaps of accepted #339 in ambient dimension two:
no actual-vertex catalogue, strict target exposure, independent coordinate,
normalized ordering, favorable convex chain, adjacency graph, rank bound or
short-route oracle is supplied. The exact finite-hull/H identity and actual
endpoint extremality remain assumptions. An algorithm producing C from an
arbitrary H description is not part of this statement. Nor is computational
efficiency of the classical choices or the Python implementation asserted.

This is a formal constructive proof of classical planar geometry, not a new
historical polygon-diameter theorem. It does NOT solve the arbitrary-dimensional
Polynomial Hirsch mission. The parameter m is the displayed original row count;
a separate formal irredundant-facet-lattice count is not asserted. No shortestness
against every arbitrary walk, all-facet locking, or global path injectivity is
added to the public conclusion.

## 1. Count actual vertices against original inequalities

Reuse the accepted #327 active-kernel and affine-line incidence lemmas. Apply
them in the AMBIENT plane N=top, not in a possibly lower-dimensional chosen
residual space. Every actual vertex has at least two active original rows with
nonzero restrictions to that plane: otherwise their joint linear evaluation
would not be injective, contradicting the finite-perturbation extremality lemma.

Every original row with nonzero planar restriction has an affine line as its
equality set, and a line contains at most two extreme points of any ambient
convex body. The latter statement does not assume a polygon catalogue.

Double-count these actual vertex/row incidences. If V is any finite collection
of actual original extreme points and I contains the nonzero original rows,

    2 |V| <= sum_(x in V) |active_nonzero(x)|
          = sum_(i in I) |{x in V : A_i x=b_i}|
          <= 2 |I| <= 2m.

Therefore |V| <= m. Zero rows are excluded on BOTH sides. This argument applies
even to a segment or point represented by planar inequalities; it does not
silently assume ordinary ambient interior or a simple/full-dimensional body.
The proof specializes the already accepted incidence mechanism, avoiding the
looser m+1 statement used for arbitrary residual subspaces in #327.

## 2. Recover the entire actual-vertex hull

Set V to the finite filter of C consisting of actual extreme points of P.
Mathlib's extremePoints_convexHull_subset shows that every actual extreme point
is already in C, so this filter is the COMPLETE vertex set, not a sample.

The hull of finite C is compact and convex. Krein--Milman identifies P with the
closure of the hull of its extreme points. V is finite, so its convex hull is
already closed. Hence conv(V)=P. This is a use of existing Mathlib theorems,
not a newly assumed completeness certificate or an experimental numerical claim.

## 3. Derive the exposure and independent coordinate

For u != v the complete finite set V contains a non-target point. The unchanged
accepted strict_vertex_functional proof separates v from the hull of the other
vertices and derives a linear h satisfying

    h(x-v)>0 for every x in V except v.

In particular h is nonzero. Write h(z)=a z_0+b z_1 and construct

    e(z)=-b z_0+a z_1.

The determinant is a^2+b^2 != 0. Explicit scalar algebra proves that the pair
(h,e) is injective. No basis-choice or independent-chart premise is added.

## 4. Prove the radial coordinate injective, then sort it

Use w(x)=e(x-v)/h(x-v) on V without v. Suppose two different original vertices
x,y have the same w. Apply #339's strict_chord argument with both outer points
chosen as y and weights 1,0. Original extremality forces

    1/h(x-v) < 1/h(y-v).

Swapping x,y gives the opposite strict inequality. This contradiction proves
injectivity; no ray-uniqueness hypothesis is assumed. The strict-chord lemma
allows identical outer points and nonnegative weights, so this specialization
preserves its exact accepted hypotheses.

Take the finite image of w, use Mathlib's orderIsoOfFin to enumerate it in
increasing order, and recover its unique vertex preimages. The resulting p on
Fin(n+1) lists exactly V without v and has strictly increasing normalized
coordinates. In particular |V|=n+2. The input C need not have any order, may be
highly redundant, and is never substituted for the complete extreme-point set.

## 5. Apply the accepted ORIGINAL-edge construction

The chart, strict exposure and independent coordinates are now outputs of the
preceding derivation. Feed them to the unchanged accepted #339 original_routes
namespace theorem. It derives strict inverse-height convexity and whole original
exposed edges, then constructs the shorter of the two boundary walks from source
index k to v. Its length is

    L=min(k,n-k)+1,    so 2L<=n+2=|V|<=m.

The public theorem exports the actual finite sequence and its original vertex
and nondegenerate IsExposed-segment properties. Equal endpoints use the length
zero sequence directly. The singleton non-target chart gives the segment case.
No original edge is replaced by an edge of an auxiliary or expanded graph.

## Reuse and verification boundaries

The complete accepted #339 namespace prefix is reused byte-for-byte, omitting
its former public solution and print commands. Selected accepted #327 helpers
are also copied without editing their declarations or proof bodies: finite
margin, strict exposure, active kernel, affine-line cardinality, nonzero active
incidences, and row slices. New namespace wrappers only control scope. Accepted
public targets are not resubmitted. Source identities are recorded separately.

The new public preamble is imports/open/options only. The top-level solution
has the exact type in problem.json. No new axiom, admission or own-target import
is used. Eight transitive axiom reports cover inherited original routes, the
original-row count, complete vertex hull, independent coordinate, normalized
injectivity, sorted enumeration, final assembly and public root.

No lean/lake/elan executable was found on PATH or within the checked installation
locations; both release and raw toolchain hosts failed DNS. Static source/type
checks and rational tests are not local Lean compilation. A single carefully
prepared complete pinned compiler/axiom/publication gate is requested. Any
failure will be preserved, not replaced by a claim based on clean helpers.
Lean 4.30.0, Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f, strict protocol
0.10.8 and the verifier/publisher credential split remain unchanged.

## Executed supporting tests

The new standard-library Fraction suite starts from original H rows and redundant,
unordered finite hull generators. It reconstructs actual vertices by complete
row-pair intersection enumeration, rejects nonzero recession directions, checks
the finite-hull equality, derives target exposures and independent coordinates,
sorts normalized actual vertices, and constructs the two counted boundary arcs.
A separate consumer reconstructs H vertices and original adjacency without
calling the producer; it checks every delivered step and the original-row bound.

The 14-model small suite includes triangles, squares, pentagons, heptagons,
eight invertible shears/translations, a segment, and a point. The larger case is
a 32-vertex planar polygon with four targets and 36 original rows. Rows include
positive rescalings, loose duplicates and zero rows. C includes edge midpoints
and interior points. Across both scopes: 92 actual vertices, 150 original rows,
195 supplied generators (103 redundant), 64 target choices, 430 routes,
1434 original-edge occurrences and 64 equal-endpoint routes. There are 213
nonzero vertex/row incidences and 28 zero rows, deliberately excluded from counts.
Eleven malformed-certificate/invalid-premise controls are rejected.

Independent BFS comparisons agree on these fixtures, but shortestness is not a
public formal conclusion. These computations are supporting tests, not proof by
sampling, Lean extraction, formal verification of Python/JSON, or a high-dimensional
route experiment. The large case is 32 VERTICES in the plane, not dimension 32.
Full report/fixture pairs and the standalone reproduction script accompany the
export. Clean repeated execution is recorded separately rather than assumed.
