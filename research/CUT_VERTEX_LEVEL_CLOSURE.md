# Vertex-level closure under aggregate cuts

## 0. Result and verification boundary

This is written mathematical research and exact rational code, not a Lean
compilation, axiom audit or Prove2Me acceptance. It is not an unrestricted
Polynomial Hirsch proof. The development base is main
`338d1f9e1cc20df86998efa5f0dc6e92916329e8`. The existing #272 direction closure,
#274 signed-level route and separately owned #275 conditioning work are not
modified or republished.

The new interface replaces a global EDGE-DIRECTION inventory by a finite
CUT-IMAGE inventory of base vertices. It proves that coordinate alphabets stay
polynomially bounded under arbitrarily many cuts that depend on a fixed number
of variable-group totals. Cut coefficients and offsets may be arbitrary real
numbers; no denominator, numerical-gap or angle lower bound is used in the
edge count. The code uses exact rationals, not a real-arithmetic oracle.

Classical inputs are compact-polytope face geometry, Caratheodory's theorem,
and the coordinate-extreme diameter argument underlying Kleinschmidt--Onn.
The last argument is already used in #274 and is credited, not claimed new.
Here it is connected to a NEW explicit post-cut alphabet and an original-edge
constructor for normals that need no longer be signed coordinate roots.
No claim of historical priority for every equivalent corollary is made.
For a box base there can be sharper direction-based bounds; the purpose here
is to handle few-level bases whose actual direction inventory is exponential,
not to claim a best-known estimate for each included subclass.

## 1. The cut-image alphabet theorem

Let P be a compact polytope in R^d. Every coordinate of every vertex of P is
in a common finite set Lambda, of size ell. This is a REAL hypothesis about
ALL base vertices, not a list inferred from visited samples. Let

    Q = P intersect {x : Cx <= h},

where C has s rows, and assume Q is nonempty. It may be nonsimple or have
smaller affine dimension than P. For each linearly independent r-row set I
of C, let Omega_I be any finite cover of

    {C_I v : v is a vertex of P}.

Construct a new alphabet as follows. Include Lambda. For every I with
1<=r<=min(d,rank C), and every affinely independent r+1-element set
z_0,...,z_r in Omega_I, solve

    sum_j alpha_j=1,   sum_j alpha_j z_j=h_I.                 (1)

When all alpha_j>=0, include every sum

    sum_j alpha_j lambda_j, lambda_j in Lambda.              (2)

**Theorem.** Every coordinate of every vertex of Q belongs to this alphabet.
In particular, if |Omega_I|<=M for all I, its size is at most

    K <= ell + sum_(r=1..min(d,rank C))
                    binom(s,r) binom(M,r+1) ell^(r+1).       (3)

The set is generally an OVERCOVER. It need not equal the realized coordinate
values of Q, and no claim that all independent image simplices lift to actual
base faces is needed.

### Proof

For a vertex x of Q, let F be the minimal base face whose relative interior
contains x, and put r=dim F. If r=0, x is an original vertex. Otherwise the
active cut normals restricted to lin(F) have rank r. If they did not, a nonzero
direction in their common kernel, in both signs and sufficiently small, would
stay within F and satisfy every inactive cut strictly. That contradicts x being
a vertex of Q. Choose r active rows I with independent restrictions. The affine
map C_I is therefore injective on aff(F).

Caratheodory expresses x as a convex combination of at most r+1 affinely
independent vertices of F. Extend these vertices, if necessary, to an affine
basis of F and give the extra vertices zero coefficient. Their r+1 images
under C_I are affinely independent. Their coefficients are the UNIQUE solution
of (1), are nonnegative, and each coordinate of x has the form (2). The complete
finite enumeration therefore contains it. This covers boundary barycentric
coefficients, simultaneous cut equalities, and lower-dimensional intersections.
It does not assume that x lies in an arbitrary preselected simplex.

This uses r rather than the r+1 base-direction allowance for EDGES in #272:
a new VERTEX in an r-dimensional base face needs r independent active cuts.
The two bounds concern different objects and must not be confused.

## 2. Arbitrarily many cuts through few aggregate totals

Partition the coordinates into p groups G_1,...,G_p, optionally leaving some
coordinates unused by every cut. Suppose every cut is constant on each group:

    (Cx)_i = sum_(a=1..p) gamma_(ia) sum_(j in G_a) x_j.       (4)

The number s of cuts and all gamma_(ia),h_i are unrestricted. Equivalently,
C has at most p distinct NONZERO column vectors. Its rank is at most p,
regardless of how many added boundary rows meet at a vertex.

If n_a=|G_a|, the sum of n_a values in Lambda has at most
binom(n_a+ell-1,ell-1) possibilities. Consequently a complete joint cut-image
cover has size at most

    M <= product_a binom(n_a+ell-1,ell-1)
      <= (d+1)^(p(ell-1)).                                  (5)

Projecting this joint cover supplies each Omega_I. Equations (3)--(5) are a
polynomial in d and s for FIXED p and ell. There is NO fixed-s requirement.
The coefficients can tend to zero, grow arbitrarily large, or make image
simplices nearly singular: the number of possible exact values, rather than
separation between them, is the resource being bounded.

If Lambda is an equally spaced ell-level grid, group sums have only
(ell-1)n_a+1 possible values. Thus

    M <= product_a ((ell-1)n_a+1) = O(d^p)                    (6)

for fixed ell,p. The resulting edge bound below is
O(s^p d^(p(p+1)+1)). For a full-dimensional final Q with m genuine facets,
mathematically delete redundant added cuts. At most m added rows remain,
removing rows cannot increase the number of distinct column types, and d<m.
Hence this recognized class has the facet-only bound

    diameter(Q) = O(m^((p+1)^2))                             (7)

for fixed p and a fixed grid alphabet. For a non-equally-spaced fixed alphabet,
the same argument gives exponent (p+1)(p(ell-1)+1). These are deliberately
coarse class bounds, not best-known bounds for every contained subclass.
The code reports its actual H-row count and does not silently perform general
irredundancy classification. Lower-dimensional outputs retain the supplied
ambient-dimension bound, not an unproved intrinsic-facet reformulation.

One can replace (4) by any independently established small finite cut-image
cover; (1)--(3) are the more general statement. The executable discovers the
joint column groups directly from C and exactly binds all original rows. It
does not accept a user-asserted alphabet for an arbitrary base.

## 3. Rank counting gives actual original-edge paths

Let a compact polytope's vertex coordinates lie in an ordered alphabet of K
levels. At two current vertices u,v in the same retained face, fix a coordinate
j. Let their global level ranks be a,b, between 0 and K-1. If a+b<=K-1, move
both along strictly coordinate-DECREASING edges to the minimum-j face. Otherwise
move both along strictly coordinate-INCREASING edges to the maximum-j face.

The combined number of steps is at most K-1: in the minimum case it is at most
(a-c)+(b-c)<=a+b; in the maximum case it is at most
(c-a)+(c-b)<=2(K-1)-a-b. Here c is the actual rank of the chosen coordinate
extremum. Strict coordinate changes spend at least one rank, regardless of
how tiny the real change is.

Both fronts reach the SAME exposed coordinate face, not necessarily the same
vertex. Retain that face and continue with the next coordinate. After at most
d coordinates they coincide. Join the first front's path to the reverse of
the second. Starting inside the minimal face containing the two requested
endpoints preserves all common original facets. Thus

    length <= d(K-1).                                      (8)

This is the classical coordinate-extreme argument applied to ranks. It does
NOT geometrically round or nonlinearly move the vertices to integer coordinates.
It permits changing and reversing objectives. A single globally monotone path
and global shortestness are NOT asserted. Compactness is essential: the
coordinate extrema must be attained and every nonoptimal vertex must have an
improving bounded incident edge.

### Original-H producer and consumer

Recognized bases are [0,1]^d and fractional stable-set systems

    0<=x_i<=1,  x_i+x_j<=1 for the listed graph edges.

The latter have levels {0,1/2,1}. A proof is short: active equations in a
component are x_i+x_j=1. If a zero/one box anchor exists, the component is fixed
to alternating zero/one values. If an unanchored component is bipartite, a
small alternating motion contradicts extremality. Otherwise an odd cycle
forces all values to 1/2. This is a complete vertex argument, not a sample
or an assertion that the graph's integral stable-set polytope is available.

The code groups the ACTUAL cut columns and enumerates their finite grid images.
It checks only row sets up to the exact cut rank, not all 2^s subsets. It forms
(1), rejects singular image simplices, keeps nonnegative barycentric solutions,
and evaluates (2). Zero coefficients are removed and permutation-equivalent
weight lists are merged. These are savings, not changes to the complete cover.
Explicit spectrum and assignment caps fail before returning a partial alphabet
as complete.

For a coordinate leg, a global original-row support LP supplies an attained
coordinate extremum and feasible witness. Its difference from the current
vertex gives a feasible improving tangent direction. At a vertex, minus the
sum of active row normals is strictly positive on every nonzero feasible ray.
Normalizing it to one yields a bounded tangent section. An exact LP maximizes
the coordinate direction there. If the optimizer is not extreme, successive
coordinate optimizations on its optimum face isolate a real extreme ray.
This uses exact equality constraints, not a guessed finite epsilon. At most
d+1 such LPs are used per edge. The existing capped Bland solver is unchanged;
no polynomial internal-pivot bound is claimed.

Every step extends to its maximal ORIGINAL-H endpoint. The consumer checks
feasible endpoints, d independent original tight rows at every vertex, d-1
common independent original rows at every edge, and the exact coordinate
monotonicity/rank charge. Right-inverse identities certify those ranks. At each
phase a nonnegative original-row dual proves the chosen coordinate extreme
in the currently retained face. The global alphabet is recomputed independently
of the route. All initial common original rows remain tight.

The positive consumer invokes no LP or tangent-ray discovery. It DOES recompute
finite spectrum construction, affine-image elimination, and rank-certificate
matrix products. Its exact arithmetic/JSON implementation is not Lean-verified.
The route uses at most (d+1)L+d LP queries; this is an oracle-query count, not
a guarantee on the solver's internal pivots or a strongly polynomial LP method.

## 4. An exponentially directional family after a dense extra cut

For d>=4 and 3/2<B<2 let

    Q_d(B)={x>=0: x_i+x_j<=1 for all i<j, sum_i x_i<=B}.      (9)

The code includes redundant upper rows x_i<=1; they are NOT additional genuine
facets. There are exactly d+binom(d,2)+1 genuine facets: each lower or pair
facet has a positive relative-interior witness with the cut strict, and the
new facet has the symmetric strict-base point x_i=B/d.

The base has three coordinate levels and the cut has ONE column type. Its
cut-image grid is {0,1/2,...,d}. Since B is between 3/2 and 2, a bracketing
image pair has four possible lower values and 2d-3 upper values. Each positive
barycentric pair contributes at most six new nonconstant coordinate values,
in addition to the original three. Therefore K<=48d-69, and (8) is quadratic
in d for this family. The actual computed cover is smaller.

The final polytope nevertheless has at least 2^(d-1)-d DISTINCT ACTUAL edge
lines. For every S containing 0 with |S|>=3, the base edge from e_0 to
(1/2)1_S is certified by the d-|S| zero rows and |S|-1 rows x_0+x_i=1.
Their rank is d-1. The edge survives or is shortened by the cut. Its direction
has support S, so different S give different lines. No enumeration of these
exponentially many directions is required by the alphabet constructor.

At d=8,16,24, with B=3/2+2^-120, the computed K is 263,583,903 and the
coordinate routes have 10,26,42 edges. At d24 the direction lower bound is
8,388,584, while the level bound is 24*(903-1)=21,648. This is a separation
between certificate resources, not an improved best diameter bound for (9).

### Important adverse result: common-face preservation can be expensive

Put r=d-2, b=B-1 in (1/2,1), t=b/r. The requested endpoints are

    u=(1-t,t,...,t),  v=(t,...,t,1-t).

Their minimal common face has x_0+x_(d-1)=1 and sum x=B. Write a=x_(d-1)
and y=(x_1,...,x_(d-2)). Intrinsically it is

    sum y=b,  0<=y_i<=a,  y_i<=1-a.                         (10)

The shortest route INSIDE this face has exactly 2d-6 edges. This is not its
unrestricted distance: u -> e_0 -> e_(d-1) -> v is a THREE-edge original path
leaving the common cut facet. For d>=5 it is shortest. The executed coordinate
routes attain 2d-6, so the distortion relative to unrestricted shortest distance
is unbounded as d grows. This is retained as an adverse result, not advertised
as global shortestness.

Here is a complete face-level proof. For a<1/2, every vertex of (10) has a=b/q
and y=(b/q)1_S for a set S of q>=2 labels. For a>1/2 take the reflected vertices.
At a=1/2 exactly one y equals 1/2, one equals b-1/2 and the others vanish.
These assertions follow by counting independent active bounds with sum y fixed.

Two lower-half vertices are adjacent exactly when their support sets differ
by one label. A lower-half vertex can meet a middle vertex by an edge only
when its support has size two. There is no edge directly from the strict lower
half to the strict upper half: their common bounds are only the zeros, too few
for a one-dimensional face. Hence any in-face path must remove r-2 support
labels, use at least two middle-transition edges, and restore r-2 labels.
This lower bound 2r-2 is attained by successively removing labels down to a
pair, passing through its middle vertex, and reversing the construction.

For d>=5 there is no unrestricted two-edge shortcut. Both endpoints are simple.
A neighbor leaving their common face must release either the cut facet or the
shared pair facet. Releasing the cut leads uniquely to e_0 at u and e_(d-1) at
v; these differ. Releasing the pair leads respectively to a cut vertex with
last coordinate zero and one with first coordinate zero; these also differ.
A mixed choice cannot coincide because only one keeps the cut tight. Inside
the common face the minimum is 2d-6>2. Thus the explicit three-edge route is
unrestricted shortest. For d4 the in-face and unrestricted distance are both2.
The tests independently reconstruct these complete local face graphs, and also
complete original graphs for d4,5,6 using the proved clique/one-cut classification.
They do not enumerate large complete graphs.

For clarity, the complete original-graph classifier used in the small checks
also has a direct justification. The uncut complete-graph fractional stable-set
polytope has vertices 0, e_i, and (1/2)1_S for |S|>=3, by the active-component
argument above. For 3/2<B<2, only 0, e_i and the size-three half vertices survive.
A new vertex lies on a cut-crossing old edge. From e_i those edges reach half
vertices on S containing i: their common star equalities and outside zeros
have rank d-1. The crossing point has x_i=1-t, other S coordinates t, with
 t=(B-1)/(|S|-2), for |S|>=4. A size-three half vertex can meet a larger half
vertex across an edge only by adding one coordinate: the shared complete-pair
normals on their intersection and outside-zero normals have rank d-1 exactly
then. Its cut intersection has three coordinates 1/2 and a fourth B-3/2.
Those are exactly the two new-vertex types enumerated by the test. Other pairs
of surviving/removed base vertices have insufficient common-row rank. This
establishes the small classifier's completeness separately from merely seeing
that all its proposed vertices are feasible. It does not claim that every
ambient square H-system was enumerated for those three special-family graphs.

This limitation does not invalidate a polynomial diameter proof using common
faces; its extra cost here is linear. It refutes only a blanket shortestness or
non-leaving-geodesic claim for this method and these polytopes.

## 5. Why rank alone, or one extra cut, is not enough for this alphabet method

In [0,1]^d add just

    x_0 + sum_(j=1..d-1) 2^(-j-1) x_j <= 3/4.               (11)

For every binary choice of the last d-1 coordinates, the new upper endpoint
has first coordinate 3/4 minus their weighted sum. All lie strictly between
0 and1, are vertices, and are pairwise distinct. Thus this ONE rank-one cut
creates 2^(d-1) different values in a coordinate. Its coefficient columns have
d distinct types; the grouped-image hypothesis has not been satisfied with
fixed p.

The resulting polytope is a combinatorial cube: it is a box in the last d-1
coordinates with a strictly positive affine upper bound and zero lower bound
for x_0. The same cube face incidences hold, so its graph diameter is d. This
is an obstruction to global alphabet control from cut rank alone, NOT a
Polynomial Hirsch counterexample or a slow-path claim. Tests exhaust all such
new upper vertices through d12. No hidden direction or image list is accepted
as complete after a cap.

## 6. Test scope, reproducibility, and next task

The tests use independent exact SymPy enumeration of every ambient square
H-system for nine small models. They include nonsimple vertices, an equality
slice, a point, two arbitrary cuts, nine rank-two cuts, and tiny unequal
coefficients. Every independently found coordinate and every actual small
base-vertex cut image is checked against the complete generated inventory.
Small routes are checked against independently reconstructed original graphs;
nonshortest outputs are retained. Actual counts are in the derived summary,
not inferred from the theoretical bounds.

Three larger clique cases do not enumerate the full original graph. Their
exponential direction counts and shortest-within-face/unrestricted distances
have separate proofs above. The three-edge comparisons receive original-row
edge certificates. Three small coefficient controls through2^-160 and an
8D nine-cut/rank-two case are executed separately. Cuts may be redundant in
that latter presentation; it is not given an unverified genuine-facet count.

Run the staged test suite as listed in CUT_VERTEX_LEVEL_HANDOFF.md. An initial
combined small test hit the45-second tool limit and produced no aggregate
success record; the final individually named model stages all completed.
Verification of stored JSON succeeds with LP and tangent-ray production
blocked. Finite algebraic enumeration remains intentional. Caps, false levels,
false support duals, changed input, missing edges and a stationary nonvertex
are rejected. No source/parser correctness is called Lean-extracted.

The broad polynomial statement applies to any compact few-level base with a
fixed number of cut-column types. The executable recognizes boxes and fractional
stable-set systems, not arbitrary carriers, unknown affine charts or general
integral descriptions. Neither a small alphabet nor a few-type cut description
has been established for every high-dimensional carrier. Taking a loose box
and arbitrary original facets typically gives p growing with d, so (3) is no
longer polynomial with a fixed exponent. That is a genuine class restriction,
not a dependence on rational denominators within the class proved here.

During finalization main advanced to af9d1ea0e2d8d07c2b1021083e2e6cfe81b20e32.
The distinct concurrent AFFINE_LEVEL_BARRIER.md now proves that some bounded
Klee--Minty cubes require an exponential global level inventory in EVERY
injective affine chart, despite true diameter d. That argument is credited
to its author and left unchanged. It is stronger than this packet's simple
rank-one-cut example, which concerns the displayed coordinate only. A universal
small GLOBAL alphabet obtained by affine preconditioning is therefore not an
open premise to try again. The present positive cut-stability theorem retains
its explicit few-level-base/few-column-type hypotheses and is consistent with
that obstruction. A general continuation must use face-adaptive or route-local
levels, or a different invariant, without assuming their total cost is small.

## References and relation to the live project

Peter Kleinschmidt and Shmuel Onn, *On the diameter of convex polytopes*,
Discrete Mathematics102(1),75--77(1992), DOI10.1016/0012-365X(92)90349-K.
The coordinate-extreme rank proof is explained here and already used by #274.

Alexander E. Black, *Monotone Diameters of Lattice Polytopes*,
arXiv:2609.08647 (2026). Its distinctions matter: small lattice alphabets do
not imply polynomial MONOTONE diameter in general, and compactness cannot
simply be discarded. This work promises neither such extension.

#272 supplies unchanged exact rank/right-inverse utilities and its separate
direction-cover theorem; #274 supplies the project precedent for finite-level
routing. #275's all-affine conditioning barrier and signed-gain recognition
remain independently owned. No competing proof or resubmission is included.
