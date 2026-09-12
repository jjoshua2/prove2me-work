# Coupled positive-feedback boxes: actual edges without product separators

## Status and position in the existing work

This is an independent continuation past #204. The source branch starts at
main `a42d88d5a822428e9bb3965a7188e91ff06951d1`, after verified #203. No files
from #204 are changed or required. Existing source, workflows, pins, STATUS.md,
credentials and platform records are unchanged.

The three new Lean files are **uncompiled mathematical proof candidates**.
They contain no proof holes, but their elaboration and axiom closure require
the pinned local gate. The proofs below do not assume acceptance of a new
platform theorem. Exact Python certificates are checks, not Lean proof terms.

What is new for this repository is not the classical theory of M-matrices or
the elementary diameter of a cube. It is an ordinary-edge derivation from a
small inequality certificate, automatic normal-form recognition, exact
same-pair carrier elimination, and application to the infinite cyclic family
which the preceding positive-projective product criteria cannot split.
There is also a noncubical extension to monotone cuts, with actual new-vertex
route checking. See Section 8 for exact formalization boundaries.

## 1. Direct theorem for coupled boxes

Let C be a d by d nonnegative real matrix, b strictly positive, and suppose
there is a positive vector w satisfying Cw<w coordinatewise. Define

    P(C,b) = { x : 0<=x_i and x_i<=(b+Cx)_i for all i }.

Then P is bounded and full-dimensional, its vertices have a bijective binary
labelling, two vertices are adjacent exactly when their labels differ once,
and their ordinary-edge distance equals their Hamming label distance. Thus

    diam(P(C,b)) = d.                                           (1)

The formal upper-bound statement includes dimension zero, where the feasible
set is a singleton. The numerical CLI supports positive dimension only.
No bound on the number of nonzero entries of C, directed cycles, normal-matroid
connectivity, or projective separators is assumed. Row sums may exceed one.
A weighted condition is essential: it is NOT silently replaced by C*1<1.

### 1.1 The weighted maximum principle

If z<=Cz, then z<=0. Otherwise choose a coordinate maximizing z_i/w_i with
positive value t. Thus z<=t*w and equality holds at that coordinate. Positivity
of C gives Cz<=t*Cw<t*w there, contradicting z<=Cz.

Applying this to -z shows

    (I-C)z>=0 implies z>=0.                                    (2)

It follows that I-C is injective, hence invertible in finite dimension, and
its inverse is nonnegative. The same argument works for every row-masked
matrix C_S=D_S*C because C_S*w<w. Thus one vector proves all 2^d complementary
systems invertible; the proof does not enumerate those systems.

### 1.2 Every label has exactly one feasible vertex

For S subset {1,...,d}, let v_S solve

    x_i=0                    (i not in S),
    x_i=(b+Cx)_i             (i in S).

Equivalently,

    (I-D_S*C)v_S = D_S*b.                                    (3)

By (2), v_S>=0. Its selected upper equations hold. For i not in S its upper
inequality is strictly slack, since x_i=0 while b_i+(Cx)_i>=b_i>0. For i in S,
x_i>=b_i>0, so its lower inequality is strictly slack. Each vertex therefore
has exactly the prescribed d tight inequalities and no others. Their normals
are independent by invertibility, and v_S is an extreme point.

The all-upper point v_all is a coordinatewise upper bound for P. For x in P,
subtract its upper inequalities from the equality for v_all and apply the
maximum principle to x-v_all. Hence 0<=x<=v_all, proving boundedness. A small
positive multiple of w is strictly feasible, proving full dimension.

There are no extra vertices. At a feasible point opposite inequalities in one
pair cannot both be tight. If a vertex omitted one pair entirely, at most d-1
rows would be active. A nonzero vector annihilating those rows gives a small
two-sided feasible perturbation, a contradiction. The new Lean candidate
proves this with an explicit complementary-basis direction and a finite
perturbation lemma adapted from PolynomialVertexSpan.lean.

### 1.3 Why a one-bit change is a genuine ordinary edge

Let S omit i and T=S union {i}. The two vertices retain d-1 independent
selected equalities. Their shared equality set is an extreme face of P.
In the S-basis its solutions form an affine line parametrized by x_i. On this
line, write every feasible z as

    z=(1-theta)*v_S+theta*v_T,   theta=z_i/(v_T)_i.

The lower constraint gives theta>=0. The i-th upper slack is

    (1-theta) * [ b_i-((I-C)v_S)_i ],

whose bracket is strictly positive. Feasibility gives theta<=1. The face is
therefore EXACTLY the segment between v_S and v_T, not merely a path or a
circuit segment. This proves ordinary adjacency in the repository's `Adj`.

Flipping each differing bit once gives at most d edges. These are active-row
label changes: multiple numerical coordinates can move during one edge.

For the reverse assertion, take the midpoint of any v_S,v_T. Exactly the
common active rows are tight there; every other row is strictly slack. Those
common rows are independent, so the smallest common face has dimension
|S symmetric_difference T|. An edge has dimension one. Hence every ordinary
edge changes exactly one bit, and no route can beat Hamming distance.

The Lean candidate proves complete vertex classification, the forward one-bit
edge theorem and the d upper bound. The reverse-edge characterization and
exact Hamming lower bound are proved here and regression-tested; they are
not extra Lean declarations in this packet.

### 1.4 Boundedness already forces a positive weight for this matrix class

For C>=0,b>0, assuming P is bounded instead of supplying w is sufficient.
P is nonempty (contains 0) and closed, so maximize sum(x_i) on compact P.
If any upper inequality at a maximizer were slack, increasing its coordinate
slightly preserves every other upper inequality because their off-diagonal
coefficients are nonpositive. Its own inequality remains feasible for a
sufficiently small positive increase. This strictly increases the objective.
All upper rows must therefore be tight. The maximizer z=b+Cz is positive and
Cz=z-b<z, so w=z is a witness.

This converse is a mathematical proof here, not an additional Lean theorem.
The checker instead solves (I-C)w=1 and verifies w>0 and Cw<w exactly.
If the solve or check fails it reports NOT CERTIFIED, never large diameter.

## 2. Automatic recognition at a supplied simple vertex

The input is an exact 2d-row H-description A*x<=B and a supplied simple
vertex p. A portal already known to be a parent vertex is a natural anchor.
No vertex-discovery algorithm is claimed.

Take the d tight rows L at p and introduce their slacks as coordinates:

    z = -A_L*(x-p) = T*(x-p).

Verify T is invertible. All remaining right-hand sides are strictly positive.
In these coordinates, test whether each remaining row has exactly one positive
coefficient, all others nonpositive, and these positive coordinates give a
bijection with {1,...,d}. Divide by the positive coefficients. This produces

    -z_i<=0,       z_i - sum_j C_ij*z_j <= beta_i,
    C_ii=0, C_ij>=0, beta_i>0.

Recover w by one exact linear solve and check its strict inequalities. A
separate verifier rechecks every original row, the full row partition, both
coordinate inverse identities, the positive row scales and w. It never calls
the recognizer or an optimizer. No row is dropped and no approximate zero
threshold is used. Redundant/additional rows are not silently ignored.

This requires a polynomial number of rational arithmetic operations at the
supplied anchor (ordinary dense elimination and matrix operations). The
certificate has polynomial size. No claim about optimum bit complexity is
needed. A poor anchor can fail even when another representation is easy;
failure is not a completeness or geometric nonexistence certificate.

## 3. Constructing routes, not just bounding them

For each requested signature solve (3), map the answer back through T^{-1},
and flip differing bits one at a time. A d-step route requires at most d+1
linear solves, not enumeration of 2^d vertices.

The independent route checker verifies feasibility and full active rank at
every returned vertex. At every step it verifies d-1 independent shared tight
rows and distinct endpoints, certifying an actual segment edge. It also checks
that each flipped label moves toward its target and is never revisited.

The tests include an explicit 32-edge route in a 32-dimensional cyclic box,
without enumerating its 2^32 vertices. A 24-dimensional cycle with gain 999/1000
still routes in 24 steps: no condition-number-dependent length enters (1).

## 4. An infinite family with NO positive-projective product split

Let d>=3, b_i>0, g_i>0 and gamma=product_i g_i<1, and take cyclic feedback

    0<=x_i<=b_i+g_i*x_(i-1 mod d).                            (4)

The weighted condition holds; for uniform g_i=epsilon in (0,1) one may use w=1.
For general positive gains with product below one, positive diagonal scaling
makes all gains gamma^(1/d), or use the exact positive solve above. The latter
avoids introducing irrational certificates for rational data. Equation (1)
therefore gives diameter exactly d for the ENTIRE family.

This family admits no nontrivial projective product decomposition. Here is a
proof, not an extrapolation from the four-/five-dimensional tests in #204.

The only disjoint facet pairs are the lower and upper facets with the same
index, by the binary face structure proved above. Facets from different factors
of a Cartesian product always meet. Consequently every putative product
partition must keep each opposite pair together. It is enough to consider a
nonempty proper subset S of the d PAIRS and its complement T.

Let k>=1 be the number of cyclic runs of S; T has the same number of runs.
Let a=1 if |S|>k, else 0, and c=1 if |T|>k, else 0. The homogeneous row span
of all paired rows with indices in S has rank

    rank(R_S)=|S|+k+a.                                      (5)

To see this, the lower rows supply the |S| independent spatial directions e_i.
Subtracting them from the upper rows leaves (-g_i*e_(i-1),-b_i). Each boundary
predecessor outside S supplies a distinct independent outside spatial direction;
there are k. An internal predecessor supplies the constant homogeneous direction,
which is independent of all boundary directions; such a predecessor exists
exactly when |S|>k. If none exists, the k boundary vectors already account for
all remaining rank. All gains and b_i are nonzero, so no zero coefficient or
cancellation is being ignored.

Similarly rank(R_T)=|T|+k+c. Thus

    rank(R_S)+rank(R_T)=d+2k+a+c >= d+3.                     (6)

For k>=2 this is immediate. For k=1 and d>=3, at least one of S,T has an
internal predecessor, so a+c>=1. The full homogeneous span has dimension d+1,
therefore the two spans intersect in dimension at least TWO. A projective
product partition must intersect in exactly the one-dimensional infinity
line. This contradicts (6). General invertible projective coordinate changes
preserve these ranks; affine changes introduce no exception.

All upper facets still share the all-upper vertex. At target 0 the old
shortest-region repair uses at most two cut labels, so g_support>=d-2.
Thus (4) combines growing deficit, connected affine normal structure, and
NO projective product split with an actual d-edge graph diameter. For d>=4
it also cannot be a small-excess leaf in the old recursive tree.

The rank formula was checked for every pair partition in dimensions 3 through
9 (501 partitions). Independent all-ROW partition searches in dimensions 4
and 5 again find zero rank-one candidates (638 partitions total). The infinite
argument is (5)-(6), not those finite experiments.

## 5. Actual common carriers remain positive-feedback boxes

This class is closed under all faces, not just whole-polytope routing.
Let Z be the common lower labels, U the common upper labels, and F the
remaining/free labels of the SAME two endpoint signatures. Put

    R=(I-C_UU)^(-1),
    h_U=R*b_U,        E_UF=R*C_UF,
    b'=b_F+C_FU*h_U,
    C'=C_FF+C_FU*E_UF.                                    (7)

Set x_Z=0, x_U=h_U+E_UF*y, x_F=y. This affine embedding identifies the face
ONTO P(C',b'). The lower constraints on U are automatic because h_U>0,E_UF>=0;
the upper constraints on Z are automatic because b_Z>0,C>=0. The upper equations
on U hold exactly, and the remaining upper rows are precisely (7). The free
coordinates supply a left inverse, so the embedding is injective.

The principal inverse R is nonnegative by the same maximum principle. Hence
b'>0 and C'>=0. Moreover R*C_UF*w_F<=w_U, and therefore

    C'*w_F <= C_FF*w_F+C_FU*w_U < w_F.

So the restricted parent weight is already a valid child witness. Diagonal
entries of C' may be nonzero but are below one; dividing row i by 1-C'_ii
returns the zero-diagonal CLI normal form without losing weighted contraction.
Empty U is handled without attempting a zero-size inverse; empty F is the
singleton face and costs zero.

The generated face certificate checks the Schur equations, signs, row scales,
and child weighted inequalities independently. For the exact starting and
ending signatures the face dimension is their Hamming difference h, and its
route cost is h. No different path, support or portal pair is substituted.

The universal Schur-closure proof is in this note. Individual rational
certificates are checked by code, not compiled to Lean proof terms. The new
Lean clipping adapter accepts the explicit algebraic PositiveBoxImage model
of each actual carrier and returns

    D + sum(actual carrier dimensions) <= D+d*r.            (8)

Positive projective chart transport from verified #203 is allowed around a
certified box model, at no added edge cost. It does not assert existence of
such a model for arbitrary carriers.

## 6. Beyond cubes: one additional monotone cut

Let Q=P(C,b) intersect {a*x<=beta}, where a>=0 in the certified box coordinates
and the cut leaves a nonempty set. Then

    diam(Q) <= d+2.                                        (9)

This is a noncubical family in general: the extra inequality creates vertices
inside parent edges and removes some parent vertices.

First, v_S<=v_T whenever S subset T. Indeed, apply the nonnegative inverse
(I-D_T*C)^(-1) to the difference of the two systems: its RHS is zero on S,
nonnegative elsewhere, and positive on T minus S. This proves coordinatewise
order preservation of the binary vertex map.

Every new Q-vertex lies on a parent edge: parent active rank plus the one new
row must span dimension d. With no double active pair this means exactly one
parent pair is unfixed. Such an edge runs from v_S to v_(S union {i}), and the
cut functional is nondecreasing on it. The lower endpoint v_S is retained.
The new vertex has an ordinary edge to this lower endpoint INSIDE Q, retaining
the same d-1 independent parent equalities. An old Q-vertex is its own anchor.

For two retained parent anchors v_S,v_T, remove S minus T, then add T minus S.
The first half is coordinatewise below v_S and the second below v_T. Every
monotone cut is therefore respected. Every traversed parent edge contained in
Q remains an ordinary edge of Q. This middle route has |S symmetric_difference T|
steps, at most d. Adding at most one anchoring edge at either end gives (9).

The implementation accepts actual rational clipped-polytope vertices, recovers
their original-edge anchors, and constructs the route. Its verifier checks
every returned edge using the ORIGINAL clipped inequalities and independent
active ranks. It never treats a new vertex as an original binary vertex.

Tests independently enumerate eight clipped systems in dimensions 2 through
5, including a four-dimensional example with 21 vertices (not a cube graph).
There are 70 newly created vertices across the tests. All 1,288 constructed
routes, containing 3,539 actual edges, pass their certificates. The construction
can return a longer route than graph distance; (9) is an upper bound, NOT an
exact-diameter or optimality claim. Signed cuts outside the coordinatewise
monotone class are rejected by this extension.

### 6.1 A fixed-number-of-cuts consequence

More generally add q>=1 inequalities whose normals are nonnegative in the
box coordinates. A new vertex lies in a smallest parent face of dimension
h<=q: the q new rows can make up at most q missing ranks. The face has the
positive-feedback model (7), whose embedding has nonnegative linear part.
Its minimum/all-free-zero vertex is coordinatewise below the new vertex and
therefore retained by EVERY monotone cut.

In the face coordinates, the capped face has 2h+q rows, is bounded and
nonempty, and its edges are ordinary edges of Q. Applying the existing Larman
bound gives a route from the new vertex to that retained anchor with length
at most

    (2h+q)*2^max(h-3,0) <= 3q*2^max(q-3,0).

Join the two retained anchors by the same down-then-up d-step path. Thus

    diam(Q) <= d+6q*2^max(q-3,0),   q>=1.                   (10)

For q=0 use (1); for q=1 use the sharper direct (9). This is linear in d for
every fixed q and polynomial when q is at most a fixed multiple of log(d).
It is not a uniform polynomial when q grows arbitrarily. It is an elementary
consequence of the displayed face/rank arguments plus the existing Larman
input; no new best classical constant is claimed. Formula (10) is proved in
this note but not formalized or implemented as a multi-cut router in this PR.

## 7. What remains difficult

None of these criteria covers an arbitrary high-dimensional carrier. The
un-cut class still consists of combinatorial cubes, even when genuinely
projectively indecomposable. The monotone-cut extension is a first noncubical
continuation, but it retains a very specific signed normal form and pays an
exponential q-dependent face budget in (10).

The concrete next research target is a joint cost argument when additional
coupled cuts grow in number, or when negative feedback destroys the simple
coordinate order and complementary-basis feasibility. A failed normal-form
check, failed projective split, or large numerical condition number is not
proof of hard graph distance. Do not add any of these as an unproved cosmetic
child of the root. The universal Polynomial Hirsch obligation remains open.

## 8. Files, scope, and next verification action

Lean candidates (717 lines in this candidate):

- PolynomialPairedBasisRouting: finite perturbation, all vertices, actual
  one-bit ordinary edges, d-step route from algebraic complementary bases.
- PolynomialPositiveFeedbackBoxes: weighted maximum principle, all masked
  inverses and feasible points, positive-feedback d bound, and top domination.
- PolynomialCoupledBoxCarrierRouting: optional positive projective/affine
  image and same-selected-pair sum-of-dimensions / D+d*r adapters.

Not new Lean declarations: reverse adjacency/exact Hamming lower bound,
boundedness-to-weight necessity, infinite no-product-split ranks, Schur-face
closure, or the one-/q-cut theorem. Those have the mathematical proofs above;
the vertex/edge, cyclic-rank, face-image and one-cut consequences have the
specified exact finite regression checks. The general boundedness converse and
q>1 routing consequence are mathematical arguments only.

The local environment used for this continuation has no Lean/Lake executable.
No hosted run was used as a speculative compiler, and no Prove2Me publication
was attempted. Keep the new work draft until the NEW modules pass:

    lake build Solutions.PolynomialPairedBasisRouting \\
      Solutions.PolynomialPositiveFeedbackBoxes \\
      Solutions.PolynomialCoupledBoxCarrierRouting

Then audit all twelve printed declarations with only standard logical axioms.
The core d-bound needs neither Larman nor a small-excess assumption. Only the
multi-cut mathematical corollary (10) invokes Larman. The image adapter uses
verified #203 transport. Repair Lean elaboration locally before the existing
single final hosted gate. Do not alter #204's pending source to integrate this.

Reproduce the executed finite checks:

    python3 scripts/test_positive_feedback_boxes.py
    python3 scripts/test_positive_box_monotone_cut.py

The first receipt records 39 normal-form certificates, 372 independently
enumerated vertices, 774 edges, 8,184 ordered graph distances, 147 explicit
routes / 446 edges, 36 same-pair face models / 220 mapped face vertices,
501 cyclic pair-partition ranks, 638 unrestricted row-partition checks, and
28 negative controls. The second records the clipped systems and 3 additional
negative controls. Receipts do not convert tests into universal proofs.

## 9. Classical background and precise provenance

The positivity argument is standard nonsingular M-matrix/K-matrix linear
algebra. Related primary sources include:

- Jan Foniok, Komei Fukuda, Lorenz Klaus, "Combinatorial Characterizations of
  K-matrices", arXiv:0911.2171; Linear Algebra and its Applications 434 (2011),
  68-80, DOI 10.1016/j.laa.2010.08.008.
- Jan Foniok, Komei Fukuda, Bernd Gaertner, Hans-Jakob Luethi, "Pivoting in
  Linear Complementarity: Two Polynomial-Time Cases", arXiv:0807.1249;
  Discrete & Computational Geometry 42 (2009), 187-205,
  DOI 10.1007/s00454-009-9182-2.

Their linear-complementarity/unique-sink-orientation results are context, not
silently imported theorems about the current primal polytope's edges. In our
notation I-C is the nonsingular M-matrix; the upper slack as a function of x
has coefficient C-I. Do not conflate those signs or cite an LCP pivot result
as a substitute for the ordinary-edge segment proof in Section 1.3.

Repository inputs are the existing Hirsch model/route predicates, the
finite-perturbation idea in PolynomialVertexSpan, affine diameter transport,
verified positive perspective transport, and the actual DeferredClipCertificate.
Only these existing sources are imported by the new Lean files.
