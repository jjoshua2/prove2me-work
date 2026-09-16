# Signed pair cuts: coordinate-level routes beyond bounded cut overlap

## 0. Scope, provenance and verification status

This is written mathematics and executed exact research code, not a Lean
compilation, axiom audit or Prove2Me acceptance. Starting main is
`e455a8da7080786f7d622a44c80cc970f1e2922e`. Coordination comment `5691300413`
on #273 was posted and read back. No other owner's proof, source or submission
is changed. In particular, #270's blocked companion is not moved through this
work, and #210 stays untouched.

The new executable interface derives a COMPLETE finite coordinate alphabet
from signed two-coordinate equations, and constructs original-edge routes
using its ordered levels. It needs neither disjoint cuts nor a small maximum
number of simultaneously tight cuts. It also does not enumerate a global
edge-direction cover, all vertices, or complete local edge stars.

The coordinate-extreme counting principle is the classical lattice-polytope
argument of Kleinschmidt--Onn, adapted here to arbitrary finite ordered levels.
No geometric nonlinear rounding map is used. Half-integrality/signed-graph
basis arguments are classical ingredients, not claimed as new discoveries.

A literature check during this work found an important stronger EXISTING
framework: the signed-root normals satisfy a uniform distance property, so
Dadush--Haehnle's shadow-diameter theorem yields a polynomial class bound even
with UNRESTRICTED right-hand-side values. Section 7 proves that specialization
and attributes the diameter theorem. The implemented small-alphabet method is
an explicit, independently checked route construction, not the first proof
that this entire signed-normal class has polynomial diameter. Its quadratic
one-value bound and endpoint-dependent certificates need not be best known.

## 1. Exact represented class

Let P be the nonempty intersection of the unit box [0,1]^d, d>=1, with rows

    sigma_e*x_i + tau_e*x_j <= beta_e,
    i != j,  sigma_e,tau_e in {-1,+1}.

Positive rescalings of these rows are allowed: the implementation divides by
the common absolute magnitude of the two nonzero coefficients. The ORIGINAL
unscaled rows are retained for final vertex/edge certification. Extra rows
with unequal magnitudes, more than two nonzeros, or unbound claimed original
H data are rejected. Arbitrary hidden affine charts are not recognized.

Let C={c_1,...,c_q} be the distinct NONZERO absolute values of normalized beta_e.
Zero beta is allowed and needs no alphabet generator. The mathematical claims
hold for real data; code uses exact rationals. No disjointness, sparsity of the
incidence graph, simple-vertex assumption or cut-overlap parameter is imposed.
P may be lower-dimensional. Its box ensures compactness. The supplied endpoints
must be actual feasible vertices, certified by full-rank original active rows.

Code reports ORIGINAL ROWS. Redundant upper-box inequalities in the stable-set
examples are not miscounted as genuine facets. For full-dimensional P, d is
bounded by its genuine facet count minus one, so any bound polynomial in d
below is also polynomial in that count. For lower-dimensional embeddings we
retain an ambient-dimension statement, not an unjustified intrinsic chart.

## 2. Derive all vertex coordinates from the active signed graph

At any vertex choose d linearly independent tight ORIGINAL rows, normalized as
above. Build a multigraph on the d variables: a two-coordinate row is an edge,
and a box row pins one variable to 0 or 1. Consider a connected component with
n variables, r pair rows and u pin rows. Full rank and the total of d rows imply
r+u=n in each component; connectivity gives r>=n-1. Thus exactly one of two
cases occurs.

* An anchored tree: u=1, r=n-1. Propagating x_j=+/-x_i+/-beta_e along the tree
  gives each coordinate as a signed anchor (0,+1 or -1) plus at most d-1
  signed RHS terms.
* An unanchored unicycle: u=0, r=n. Propagate from a cycle root. A balanced
  cycle would leave a free scalar, contradicting independence. The cycle is
  therefore unbalanced, and its closing equation gives twice the root value
  as a signed sum of its edge RHS values. Reaching another coordinate adds
  twice the signed terms on the attached tree path. If the cycle has l edges
  and that path p edges, l+2p<=2d. Parallel edges, which give a two-cycle,
  are included.

Define S_R(C)={sum_j n_j*c_j : n in Z^q, sum_j |n_j|<=R}. Every vertex
coordinate belongs to the explicitly constructed set

    Lambda = [0,1] intersect
      (({-1,0,1}+S_(d-1)(C)) union (1/2)*S_(2d)(C)).              (1)

This is a UNIVERSAL derivation for the represented H system, not a list learned
from the visited vertices. Extra active rows, nonsimplicity and affine-hull
constraints cause no problem because a full independent basis can still be
chosen. Collisions among different expressions only reduce |Lambda|.

The integer l1-ball has exactly

    B_q(R) = sum_(j=0..min(q,R)) 2^j binom(q,j) binom(R,j)

vectors: choose its j nonzero positions, their signs, and positive magnitudes
with sum at most R. Hence

    |Lambda| <= 3*B_q(d-1) + B_q(2d).                           (2)

For fixed q this is polynomial in d and does not depend on denominators,
coefficient bit size or the separation between two distinct levels. q=0 gives
exactly {0,1}. For q=1, with positive generator c, the half-sum portion has at
most 2d+1 nonnegative terms. Integer multiples of c anchored at zero are already
in it. The +1 anchor contributes at most d terms and the -1 anchor at most d-1.
Thus |Lambda|<=4d. Values outside [0,1] and duplicate expressions are removed.

## 3. Finite ordered levels control actual ordinary-edge distance

Lemma (ordered-level form of the coordinate-extreme argument). If every vertex
of a compact polytope has its i-th coordinate in a finite ordered set Lambda_i,
then any two vertices can be joined by at most sum_i(|Lambda_i|-1) original
edges, within their least common original face.

Start with that common face and two route fronts u,v. At coordinate i write
r,s for their ranks in Lambda_i and c=|Lambda_i|-1. If r+s<=c, move both fronts
to the xi-MINIMIZER face by strictly decreasing xi edge steps. Otherwise move
both to the MAXIMIZER face by strictly increasing steps. A vertex which is not
optimal for a linear objective has an improving incident edge in that face:
its tangent cone is generated by its incident edge directions, and a feasible
point with greater objective supplies a positive direction. Compactness gives
an attained extreme value. Strict coordinate improvement uses at most the
corresponding rank difference, irrespective of actual numerical step size.

Both fronts reach the same extreme coordinate because they start in the SAME
face. Their combined cost is at most r+s in the minimum case, or 2c-r-s in the
maximum case, and the selected one is at most c. Lock that coordinate at its
extreme value and continue. The new restricted set is an exposed FACE, not an
arbitrary slice. Therefore its edges remain original polytope edges. After
all coordinates the two fronts coincide. Reverse the second leg and join.
The zero-step case and endpoint membership are explicit.

Ranks are used ONLY to count strict changes. Mapping coordinates to ranks is
not an affine operation and is NOT asserted to preserve polytopes or edges.
There is also no single fixed objective that is monotone along the final path,
and original facets can be revisited. Common original facets are never lost.

Combining this lemma with (1) yields the constructive class estimate

    diam(P) <= d*(|Lambda|-1)
             <= d*(3 B_q(d-1)+B_q(2d)-1).                      (3)

The exponent is q+1 for fixed q. The special bounds are d at q=0 and
4d^2-d at q=1. The implementation uses the actual smaller alphabet and retains
an even smaller sum of its selected endpoint rank budgets. The q restriction
belongs to this particular enumeration/algorithm, not to a claim that signed
normal polytopes with large q are unbounded in diameter; see Section 7.

## 4. Construct an improving ORIGINAL edge without enumerating a full star

At a route vertex x, let I be ALL tight normalized original rows and let
h=-sum_(i in I) a_i. Restrict the tangent cone by the old common-row equalities
and previously locked coordinates, then truncate by h*r<=1. Zero is feasible.
Every nonzero feasible tangent vector has h*r>0: equality would place it in
the common kernel of the full-rank active original rows. The truncated cone
is compact. Its nonzero vertices lie at h*r=1 and represent extreme rays of
the tangent cone of the current face.

Any homogeneous signed-pair/unit-row system of rank d-1 has a one-dimensional
kernel of the form span(s), with s in {0,+1,-1}^d. In its signed graph, all
components but one are pinned or unbalanced; the remaining balanced component
has one signed constant, and all other coordinates vanish. Thus a nonzero
truncated-cone vertex is r=s/H, where H=h*s is an integer with 1<=H<=2m and m
is the number of represented original rows. Reversing rows for common faces
and adding locked-coordinate equations preserve the same signed-root type.

Let D=2m. Distinct truncated-cone vertices, including zero, differ in some
coordinate by at least 1/D^2. Order coordinates with the current phase coordinate
first (with its desired sign), then the others. Encode this lexicographic
objective with weights 1,B^-1,..., B=4D^2+4. The entire possible tail is less
than the first nonzero difference. Therefore its maximizer is UNIQUE and is
an actual truncated-cone vertex, not a nonvertex chosen by an LP representation.
If a primary-coordinate improvement exists, the selected direction improves it.

The existing exact LP engine maximizes that objective. Travel to the minimum
positive original-row blocking ratio along its direction. Compactness supplies
a finite blocker. This gives an edge of the current face, hence an ORIGINAL
edge. As an independent safeguard, the producer certifies both endpoint ranks
and d-1 independent common ORIGINAL rows using #271's unchanged arithmetic
checker. It never equates an extension edge or a fractional LP point with an
original edge.

At a coordinate optimum, a second primary-only LP returns a nonnegative dual
with value zero. The only nonzero RHS in the truncated cone is h*r<=1, so its
dual coefficient must be zero. The remaining combination of active rows and
locked equalities is a global optimality certificate on the current face.
The two fronts' common extreme value and every earlier lock are then checked.

The route uses at most L+4d LP calls for L committed edges. Capped Bland simplex
is the inherited LP implementation; its INTERNAL pivot count is NOT proved
polynomial. No claim of a strongly polynomial simplex implementation is made.
Alphabets and certificates are polynomial in explicit input size for fixed q,
with exact rational arithmetic. Alphabet, LP and path caps fail explicitly;
they never establish a negative route result.

The consumer recomputes the represented class and complete alphabet, verifies
the given original-row path inverses, checks phase monotonicity/rank budgets,
and checks all zero-gap extreme-face dual combinations. It runs no LP, inverse
construction, elimination, neighbor discovery or route selection. It still
performs finite alphabet enumeration. Generic source correctness/JSON parsing
has not been formalized in Lean.

## 5. Completed examples: large overlap and an exponentially large direction set

### Tiny-denominator chain, with all cuts meeting

P={0<=x<=1, x_i-x_(i+1)<=theta}, theta=2^-160. Take source1 and target
((d-1)theta,...,theta,0). All d-1 cut rows meet at the target. The source and
target share no original facet. Every one of the 3d-1 rows is genuine, with
exact facet-interior witnesses checked in the test.

The polytope is simple when (d-1)theta<1. An active chain component cannot have
two box anchors: their difference would be a nonzero integer multiple of theta
of magnitude below1, inconsistent with two endpoint values in {0,1}. Therefore
the active components are singly anchored intervals and every vertex has exactly
d independent tight rows. Each edge gains at most one of the d missing target
facets, so the returned d-edge paths in dimensions16 and32 are shortest.

The complete alphabet has 3d+1 levels in these tests; the uniform level bound
is 3d^2. The 32D run has95 genuine facets,31 simultaneous cut rows,32 actual
edges and3072 as its all-pairs level bound. The much larger d*2^160 number
obtained by naively scaling into an integer box is only a LOOSE existing upper
bound, never a lower bound or a claim of best-known theory.

### Nonsimple wheel, with explicit adverse performance

For the wheel graph on d vertices impose x_i+x_j<=2/3 on every edge. The target
has every coordinate1/3 and ALL 2(d-1) cut rows tight. The source is0. Its upper
box rows are redundant; the d lower and2(d-1) graph rows are genuine. The small
alphabet is {0,1/3,2/3,1}, giving the implemented all-pairs bound3d.

The algorithm returns10 edges in dimension16 and18 in dimension32. These are
NOT shortest. The separately certified path 0 -> (2/3)e_hub -> (1/3)1 has two
original edges and is shortest because the endpoints are not adjacent. The
32D returned path also has18 original-row reentries. There is no nonrevisiting
claim, no benchmark dominance, and no extension of #273's zero-reentry theorem.
Michini--Sassano already prove the stronger diameter<=d for fractional stable
set polytopes. These wheel tests are controls of our implementation, not new
stable-set bounds.

### Mixed signs and two RHS magnitudes

An odd-cycle positive-sum block with magnitude5/7, coupled to new variables by
signed difference rows of magnitude1/17, gives nonseparable target systems with
23 and47 simultaneously tight cuts in dimensions16 and32. Returned lengths
are16 and32. Genuine-facet minimality and shortestness are NOT asserted for
these mixed examples. Their actual represented-row counts are55 and111.
Alphabet sizes and LP work are in the raw reports.

### Complete-graph family: many ACTUAL directions, not an oversized overcover

For all pairs x_i+x_j<=2/3, fix i and consider the vertex (2/3)e_i. For EVERY
subset S containing i with |S|>=3, the point (1/3)1_S is a vertex: its active
complete graph on S is nonbipartite, while outside coordinates are zero.
The two points share d-|S| outside lower rows and |S|-1 independent pair rows
joining i to S minus i, totaling d-1 independent normals. Thus their segment
is an actual edge. Distinct S give distinct lines. There are

    2^(d-1)-d

such lines, while the coordinate alphabet still has four levels. At d=32 this
is2,147,483,616 distinct ACTUAL lines and an implemented class bound96. Only
22 explicit sample edges across d4/8/16/32 are checked numerically; the count
is proved above, not enumerated. Again the known stable-set bound is stronger.
This shows why a small global direction inventory is not needed by this method.

## 6. Necessary method restrictions and current literature

Equal coefficient magnitudes matter. The deformed cube

    0<=x_1<=1,
    epsilon*x_(i-1)<=x_i<=1-epsilon*x_(i-1), epsilon=1/4,

has only RHS values0 and1 but2^d distinct last-coordinate values at vertices.
The disjoint maps z->z/4 and z->1-z/4 double the level count at each dimension.
Every choice of lower/upper bound gives a distinct vertex. The polytope is a
combinatorial cube of diameter d: the exponential level inventory refutes an
extension of THIS count to arbitrary two-variable coefficients, not Polynomial
Hirsch. Exact counts through d12 are checked. An unequal row can also approach
the span of a unit row arbitrarily closely; the angle control below then fails.

The ordinary route may reverse a leg and reset its objective at every locked
coordinate. It is not a monotone path for one fixed target objective. This
boundary is important in light of Alexander E. Black's September8,2026 preprint
`Monotone Diameters of Lattice Polytopes`, arXiv:2609.08647v1: that paper proves
exponential monotone diameter in fixed-height lattice boxes, and gives unbounded
0/1-vertex polyhedra with exponential ordinary diameter. Our level lemma requires
COMPACTNESS, and makes no fixed-objective monotonicity claim. The present tests
do not reproduce or independently verify that paper's constructions.

## 7. Stronger classical-framework corollary: no small RHS alphabet is necessary

This subsection prevents misidentifying a method restriction as the current
mathematical frontier. Let every nonzero row of a matrix be proportional to a
unit vector or to +/-e_i+/-e_j. No restriction on right sides or their alphabet
is needed for the following distance-property argument.

For ANY subset of normalized rows, the orthogonal complement of its span has
an orthogonal basis of signed indicator vectors s_C on its unpinned balanced
signed-graph components C. Pinned or unbalanced components contribute zero.
For any additional normalized root a, its squared distance to that span is

    dist(a,span)^2 = sum_C (a dot s_C)^2 / |C|.

Every a dot s_C is an integer. If a is outside the span, at least one is
nonzero, hence the distance squared is at least1/d. Since ||a||^2<=2,

    dist(a,span)/||a|| >= 1/sqrt(2d).                         (4)

Positive row rescaling leaves this relative property unchanged. Thus the
matrix satisfies the GLOBAL delta-distance property with delta=1/sqrt(2d),
including every linearly independent row subset, feasible or otherwise.

Dadush--Haehnle, arXiv:1412.6705v1, Definition4 and Lemma5, show that a basis
with this property generates a delta/d-wide cone. Any full-dimensional pointed
polyhedron with our normals has an independent active basis at every vertex,
so every normal cone contains such a cone, even at nonsimple vertices. Their
Theorem3 (equivalently Theorem11) then supplies diameter at most

    8*sqrt(2)*d^(5/2) * (1+log(d*sqrt(2d))).                   (5)

This is an EXPLICIT SPECIALIZATION OF AN EXISTING THEOREM, not a new proof of
the shadow method, an independently implemented random walk, or a historical
priority claim. It applies to full-dimensional pointed signed-normal polyhedra,
even unbounded, for arbitrary real right sides. The lower-dimensional cases of
our executable box model are instead covered by Sections2-4; we do not assert
an unchecked intrinsic projection preserves (4).

The implemented coordinate-level path can give a better explicit bound in
small-alphabet cases (quadratic at q1), but it need not match the guarantee of
a different algorithm when q is large. We have not implemented the cited
shadow algorithm or transferred its pivot bound to our Bland-based subroutine.
There is therefore NO claim that arbitrary RHS values are an open diameter
obstacle within this same signed-root class.

The separate test `check_signed_root_angles.py` compares the signed-component
projection formula with independent exact Gram-matrix projection on11,716
row/root cases in dimensions1,2,3,4,5,8. It includes8,079 positive distances and
3,637 zero distances. Lower-dimensional/rank-deficient selected row systems
are included. This supports the derivation, not a proof by finite sampling.

## 8. Executed tests, adverse records and exact reproduction

The14 independently reconstructed small original H graphs use2,253 complete
active bases,103 vertices and168 edges. Their201 selected route pairs produce
333 edges versus314 BFS edges;17 routes are nonshortest, with6 total row
reentries. The test separately classifies independent active basis components,
checks every reference coordinate against (1), and checks actual homogeneous
edge directions. The six large routes add124 edges. The wheel comparison paths
and22 sampled complete-graph edges have independent original-row rank checks.

Nineteen malformed/unsupported/capped controls are rejected. Tiny denominators,
positive row rescalings, coincident signed-pair lines, zero RHS, redundant rows,
zero-length routes and lower-dimensional systems are covered. No assertion
that the test mutations cover every malformed JSON is made.

Thirteen saved route records and two wheel comparisons replay with LP,
lexicographic objective construction, inversion, elimination, vertex-packet
production and route construction disabled. The consumer still verifies the
actual alphabet, all original path ranks and all locked-face dual certificates.

An initial combined large-test process hit the45-second command limit after
five completed models; no aggregate success was claimed. The final source uses
separate named stages, and every stage, including mixed32, completed. Full raw
reports and seven serialized fixture files accompany the download and regenerate
from the committed tests. Clean replay details and all byte hashes are preserved
separately. No partial timeout is relabeled as a negative theorem or a completed
run. No Lean, Actions or platform verdict is attached to this research.

    for s in small chain wheel mixed directions negative audit; do
      python3 scripts/test_signed_level_routes.py --stage "$s" \
        --out "/tmp/$s.json" --fixtures /tmp/signed-level-fixtures
    done
    python3 scripts/check_signed_root_angles.py --out /tmp/angles.json

## 9. Remaining unrestricted target

The new executed method handles arbitrarily overlapping signed-pair cuts by
counting coordinate levels; the classical angle argument covers arbitrary RHS
within the same normal class. Arbitrary original carriers need not have these
normals, a certified well-conditioned chart, or a small coordinate alphabet.
Unequal coefficients invalidate both the short-sum and uniform-angle arguments.
The next universal step must derive a genuinely broader structural/route-local
control, not assume one of those small parameters. #267's refutation of universally
small complete forward-stellar refinements remains intact.

### Primary references and project dependencies

- P. Kleinschmidt and S. Onn, *On the diameter of convex polytopes*, Discrete
  Mathematics102 (1992),75-77, DOI10.1016/0012-365X(92)90349-K.
- C. Michini and A. Sassano, *The Hirsch Conjecture for the fractional stable
  set polytope*, Mathematical Programming147 (2014),309-330,
  DOI10.1007/s10107-013-0723-3. Author repository:
  https://www.research-collection.ethz.ch/handle/20.500.11850/74180 .
- D. Dadush and N. Haehnle, *On the Shadow Simplex Method for Curved Polyhedra*,
  https://arxiv.org/html/1412.6705v1 , Definition4, Lemma5, Theorems3/11.
- A. E. Black, *Monotone Diameters of Lattice Polytopes*,
  https://arxiv.org/html/2609.08647v1 , submitted September8,2026.
- UNCHANGED `scripts/exact_farkas_lp.py`, blob
  ea511a79164d953792942d8be3dd3537646738d6: exact capped Bland discovery and dual
  arithmetic checks. UNCHANGED #271 `scripts/original_route_exclusion.py`, blob
  a764196e54970825823cad4575b947b507f95951: original-row path inverse checker.
