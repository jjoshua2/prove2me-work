# Original-edge routes from actual finite hulls

## Accepted status — September 21, 2026

PR #322's complete repaired proof is ACCEPTED, with trusted-publisher live_status
Proved. Theorem 5a81c2f0-e6fe-4eea-a627-0acdde34206a; submission
acd494ac-d764-4d26-972a-f92614c800d7; run 35659994840; exact proof
3fa9791c65405c57804730cac7481f28ac26f066. All eleven proof reports are standard-only.
The internal 0/1-hull corollary also compiles; it is not separately registered.
Read GEOMETRIC_COORDINATE_HANDOFF.md and the packet's accepted-evidence.md.
The following original mathematical argument and test description are retained
verbatim as preparation history; its candidate-status language is superseded by
this receipt. The theorem's assumptions and limitations have not changed.


## Result and verification boundary

This is the positive geometric adapter to accepted PR #283, not another
zonotope-completion obstruction. PR #322 contains the complete candidate
Hirsch.finite_hull_original_coordinate_routes. Consult
GEOMETRIC_COORDINATE_HANDOFF.md for the latest compiler and platform state.
The written proof below is independent of that state: a failed elaboration is
not a verified Lean theorem, and exact arithmetic tests are not compilation.

Let C be a finite subset of R^d, P=conv(C), and V the actual extreme points of P.
For any actual vertices u,v, the proposed formal result constructs an indexed
walk in V from u to v with nondegenerate whole original extreme segments and

    L <= sum_j (|{x_j : x in V}| - 1).

No supplied neighbor graph, face catalogue, improving neighbor, active rank,
connectivity, short path or simplicity premise occurs. Finiteness of C and actual
endpoint extremality remain explicit. C may include nonvertices. Lower-dimensional
hulls, d=0, coincident endpoints and nonsimple vertices are included. The ambient
dimension is d; no claim replaces it by affine dimension in the formal corollary.

## 1. A constructed improving original exposed edge

Fix an actual vertex u and a linear objective f for which some feasible point
has a larger value. Separate u strictly from conv(C minus {u}); negating the
separating functional gives h(x-u)>0 for every x in C different from u.
A linear upper bound on all generators extends to the hull, so there is an
original generator a with f(a-u)>0.

For d_x=x-u form all normalized contrasts

    B(x,z) = h(d_x) d_z - h(d_z) d_x.

Finite regularization supplies g such that g(B) is nonzero whenever B is nonzero,
and sign(g(B))=sign(f(B)) whenever f(B) is nonzero. This uses the accepted
finite-margin/dual-separation argument, not an assumed generic objective.
Choose the largest ratio M=g(d_x)/h(d_x); among its ties choose v with largest
h(d_v). Define q=g-Mh. Every generator displacement satisfies q(d_x)<=0.

If x is tied, g(B(v,x))=0. Regularity forces B(v,x)=0, hence

    d_x = (h(d_x)/h(d_v)) d_v.

The scalar is positive and at most one by the farthest-tie choice. u is the
zero-scalar case. Thus all tied generators lie on [u,v]. Conversely both endpoints
are tied. Equality in the linear support bound for a convex combination forces
its positive-weight generators to be tied. Therefore the WHOLE maximizing slice
of P is exactly [u,v], not just a subset or chord. Its endpoints are actual vertices.

To prove ORIGINAL objective improvement, suppose f(d_v)<=0. Then

    f(B(v,a)) = h(d_v) f(d_a) - h(d_a) f(d_v) > 0.

Sign preservation gives g(B(v,a))>0. But ratio maximality implies

    g(B(v,a)) = h(d_v) [g(d_a)-M h(d_a)] <= 0,

a contradiction. Thus f(v)>f(u). This construction needs neither a tangent-cone
ray list nor an inverse/neighbor oracle. The reference implementation derives h
from original supporting rows instead of invoking abstract Hahn--Banach.

## 2. Actual vertices and retained faces

Mathlib extremality puts every vertex of a finite hull among its generators.
Krein--Milman says P is the closure of conv(V). V is finite, so its convex hull
is closed; consequently P=conv(V). This derives the complete vertex catalogue.

Filtering any finite generator family at an attained linear maximum produces
its whole exposed face. For one inclusion, every filtered point is feasible and
has the maximum value. For the other, equality in the convex support bound forces
only maximizing generators. Coordinate minima use the negated coordinate.

Enumerate V without changing its real coordinates. Let an admissible finite
vertex family F mean that conv(F) is an extreme subset of P. Its coordinate
minimum/maximum subsets are admissible by the preceding support argument and
transitivity. An actual vertex of P in conv(F) stays extreme in conv(F). Apply
Step 1 inside that finite hull to construct improving exposed edges there, then
transfer extremality to P. The public type asserts whole IsExtreme original
segments. A separate assertion of original-ambient IsExposed is not included.

## 3. The two-front count

Reuse the accepted finite coordinate theorem, with actual geometry discharging
all its local graph/face premises. Rank the finite coordinate-j values from zero
to K_j=|levels_j|-1. Ranking is only a counting device; the real points and their
geometric edges are never nonlinearly rounded.

For endpoint ranks r_u,r_v, use the coordinate minimum if r_u+r_v<=K_j, otherwise
the maximum. Strict one-edge progress reaches that extreme from both endpoints;
their total edge cost is at most K_j. The two new endpoints lie in the same
coordinate-extreme face. Fix that coordinate and repeat. Induction joins the
fronts inside the retained face and sums the K_j budgets. Equal endpoints and
zero-dimensional hulls require no edges. Neither the algorithm nor the proof
asserts shortestness, vertex simplicity, facet nonrevisiting or one global
monotone objective.

## 4. Concrete positive class and remaining mission gap

For any finite 0/1 generator family, every actual vertex is a generator, so each
coordinate has at most two vertex values. The internal zero_one_routes helper
therefore gives L<=d. It is in the same Lean candidate and axiom-print list; it
is not registered as a separate public theorem. This includes arbitrary 0/1
subsets with nonsimple or lower-dimensional hull, not only full cubes.

These are classical bounds in substance. Bibliographic baseline: Peter
Kleinschmidt and Shmuel Onn, On the diameter of convex polytopes, Discrete
Mathematics 102(1), 75--77 (1992), DOI 10.1016/0012-365X(92)90349-K.
The 0/1 dimension bound is attributed to Naddef (1989), also recalled in the
primary paper Alexander E. Black, Monotone Diameters of Lattice Polytopes,
arXiv:2609.08647. That paper explicitly distinguishes ordinary compact routes
from fixed-objective monotone routes and unbounded polyhedra with 0/1 vertices.
No historical-priority or best-known-bound claim is made here.

This packet needs no integer spacing, but the total actual level inventory can
be exponential in original facets. Accepted #280 proves a corresponding
all-affine triangular obstruction. Thus this is NOT Polynomial Hirsch, an
original-H enumeration algorithm, or a polynomial-time guarantee. A universal
adaptive/route-local budget remains a separate mathematical obligation; it is
not inserted as a hypothesis and declared solved. #282 and #210 are untouched.

## 5. Exact supporting tests and reproducibility

The two committed Python scripts use exact rationals and exhaustive small-hull
support discovery. They include fourteen models: points, redundant segment and
square generators, a nonsimple pyramid, a cube, a hypersimplex, a simplex,
a rational polygon, a 2^-80 gap, and four deterministic arbitrary 0/1 subsets.

The reference derives complete facets, vertices, edges and faces using an
injective intrinsic coordinate projection and exact linear algebra. The edge
CONSTRUCTOR never reads the reference graph. It uses exhaustively derived
supporting rows, normalized contrasts and the full support-equality check.
The independent consumer checks endpoints, improvement, the entire support
maximizer set in the retained face and the original edge relation.

All 2811 local coordinate-improvement obligations pass. The 480 endpoint routes
have 690 edge occurrences versus 534 shortest-distance total. There are 134
nonshortest outputs, deliberately retained. All 690 saved certificates replay
with edge construction disabled; eleven malformed controls are rejected. These
are not independent proofs that every theorem hypothesis is necessary.

A clean two-script workspace reproduces the entire report and fixture byte for
byte. The full report and 331977-byte fixture accompany the export and regenerate:

    python3 scripts/test_geometric_coordinate_routes.py --out /tmp/geometric-routes
    python3 scripts/check_geometric_coordinate_controls.py --out /tmp/geometric-controls.json

The committed test summary is explicitly DERIVED. Python, JSON parsing, reference
discovery and the concrete certificates are not Lean-extracted or kernel-verified.
No large graph enumeration or high-dimensional execution is claimed.
