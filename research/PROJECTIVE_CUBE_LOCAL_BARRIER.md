# Every raw target-row flag can be exponentially expensive

This is a complete written argument with reproducible exact tests. It is NOT an
additional Lean instance theorem or a Prove2Me acceptance. The generic normalized-
slack route packet has its own separate verification status. No historical
priority or new classical cube-diameter result is claimed.

## 1. Original inequalities, inverse chart, and exact finite hull

Fix an integer d>=1, w_j=2^j for j=0,...,d-1, and W=sum_j w_j=2^d-1. Define

    P={x in R^d : -x_i<=0 and x_i+w.x<=1 for every i}.

These are exactly2d displayed original rows. Write q(x)=1-w.x. Feasibility says
0<=x_i<=q(x). In particular q>=0. If q=0 then x=0 and q=1, a contradiction.
Thus q>0 throughout P. Also q<=1 and P is closed and contained in[0,1]^d.

For y in the unit cube, put Phi(y)=y/(1+w.y). Its denominator is at least1.
Then q(Phi(y))=1/(1+w.y)>0, and the lower and upper slacks are

    Phi(y)_i=y_i/(1+w.y),
    1-Phi(y)_i-w.Phi(y)=(1-y_i)/(1+w.y).

Conversely, for x in P, y=x/q(x) belongs to the unit cube and Phi(y)=x.
These inverse rational formulas are continuous on their positive-denominator
regions. Their derivatives are nonsingular there, or directly the inverse maps
show they carry relatively open sets to relatively open sets.

For every S subset {0,...,d-1}, let t_S=1+sum_(j in S)w_j and

    v_S=1_S/t_S.

Every v_S is feasible. Conversely write any y in the cube as a convex combination
sum_S lambda_S*1_S (for example use independent Bernoulli product coefficients).
Let t=1+w.y=sum_S lambda_S*t_S. The numbers mu_S=lambda_S*t_S/t are nonnegative
and sum to one, and

    Phi(y)=sum_S mu_S*v_S.

Therefore P equals the convex hull of EXACTLY this finite corner family.
This proves the needed H/hull equality rather than assuming it from a graph.

## 2. Complete original vertex classification

At v_S, the tight rows are precisely lower rows i not in S and upper rows i in S.
There are d of them. To see that they determine v_S uniquely, their homogeneous
kernel equations for z say z_i=0 off S and z_i=-w.z on S. Summing with weights
and setting tau=w.z yields

    (1+sum_(i in S)w_i)*tau=0.

Its coefficient is positive; hence tau=0 and z=0. The active rows therefore have
full rank. If v_S were a strict convex combination of feasible x,y, every active
support inequality would be equality at both x and y, and uniqueness would force
x=y=v_S. Thus every v_S is extreme. Conversely every extreme point of this
finite hull belongs to its generating set. The list has exactly2^d distinct
points, because the zero-coordinate support identifies S.

In particular every actual vertex has positive q. The generic normalized-slack
packet's denominator hypothesis holds with a_i=1,D_i=-w for every original row.

## 3. All2d rows are genuine facets

The image under Phi of y=(1/2,...,1/2) satisfies every inequality strictly, so P
is full-dimensional (strict inequalities persist in a sufficiently small ball).
For lower row i, take y_i=0 and all other coordinates1/2. For upper row i, take
y_i=1 and the others1/2. Their images satisfy exactly the chosen row tightly and
every other original row strictly, by the slack identities above.

The chosen row has nonzero normal. A sufficiently small relative ball within its
hyperplane remains strictly feasible for every other row, so the corresponding
face has affine dimension d-1. Thus each displayed row is an irredundant facet;
no expensive redundant row has been slipped into the example. The argument
includes d=1, where the facets are the two endpoints.

## 4. Whole original edges, not projected chords

Take S=F union {j} and compare v_S with v_F. Let B be the complement of S. Their
common rows are lower rows in B and upper rows in F, precisely d-1 rows. Their
homogeneous kernel says

    z_i=0 (i in B),
    z_i=-tau (i in F),
    tau=w_j*z_j+sum_(i in F)w_i*z_i.

Consequently tau=w_j*z_j/(1+w_F). There is exactly one free coordinate z_j;
these common rows are independent and their equality intersection is a line.
Along the displacement delta=v_F-v_S, delta_j<0, the lower row -x_j increases
from negative to zero, and the released upper row x_j+w.x decreases from one.
The latter inequality blocks extension beyond v_S and the former blocks extension
beyond v_F. Convexity gives all points between them. Thus the entire feasible
slice of the common original equalities is exactly the nondegenerate segment.

Each common row is a supporting inequality. Equality in the sum of their slack
inequalities holds iff all are tight; hence the common slice is a whole exposed
face. With d=1 the empty sum is zero and its full maximizing face is P itself,
which is the endpoint segment. This proves these are genuine original edges.
The same argument with arbitrary S and one added/removed bit covers all cube
bit edges without assuming a projected edge is automatically an original edge.

Starting at v_[d] and removing bits0,1,...,d-1 gives d original edges to zero.
Any lower row acquired stays tight because its coordinate remains zero. For
arbitrary endpoints, flipping each differing bit once gives a route with at most d
edges and preserves every original facet shared by the endpoints. These are
explicit upper bounds; no shortestness claim is needed for this contribution.

## 5. EXACT exponential cost for every #332 eligible raw flag

Fix u=v_[d]=(1/2^d,...,1/2^d), v=0. The target has exactly d tight rows: the lower
coordinate inequalities. None is tight at u, so the shared-row set G is empty
and the initially missing target set T consists of all lower rows.

The homogeneous determining condition on a subset of coordinate rows forces
it to contain all d: an omitted coordinate gives a nonzero kernel vector. Since
#332 permits distinct lists of length at most min(d,2d-d)=d, every eligible list
is exactly a permutation of T.

Suppose a prefix has fixed some coordinates to zero and k coordinates remain.
The actual vertices on this ORIGINAL face are exactly v_S with S contained in
the remaining coordinate set. For the next lower row -x_j, values are zero when
j is absent, and otherwise

    -1/(1+w_j+sum_(i in U)2^i),

where U ranges over all subsets of the other k-1 remaining indices. Binary
subset sums are distinct, so there are exactly2^(k-1) distinct nonzero values.
They are all negative and hence distinct from zero. The raw charge is therefore
exactly2^(k-1), independently of which j is selected or of earlier order.

Every eligible order has conditional total

    2^(d-1)+2^(d-2)+...+2+1 = 2^d-1.

This is the minimum over ALL eligible lists, not a bad heuristic order. It is
exponential in the genuine original facet count m=2d. Thus a universal polynomial
upper bound on #332's specific optimized raw affine-row local-charge measure is
false. Its accepted routing theorem is not contradicted: L<=an exponential budget
allows the d-edge routes just constructed. This is no Polynomial Hirsch
counterexample, nor an impossibility theorem for all route-local invariants.

## 6. Normalized spectra remove this exact obstruction

Use the positive affine q(x)=1-w.x for every denominator. On the actual vertices,

    lower normalized slack = x_i/q(x) = 1_(i in S),
    upper normalized slack = (1-x_i-w.x)/q(x) = 1-1_(i in S).

Both spectra are exactly{0,1}. For arbitrary endpoints the generic normalized
packet derives a determining completion of at most d initially missing rows,
weight at most d, and an original-edge route bounded by that weight. This does
not use a supplied projective chart in the formal theorem; its instantiated
denominator is explicit and its positivity was proved above.

For the opposite endpoints, every determining completion contains all d lower
rows and each weight is one, so the minimum normalized weight is exactly d.
The explicit d-edge route supplies an independently checked comparator. In d64,
P has128 genuine facets, raw minimum18446744073709551615, normalized minimum64,
and a64-edge route. The huge count is a proved formula, never an enumerated table.

The new generic theorem allows DIFFERENT denominators per row, so it is not
merely a re-publication of existing #203 projective graph transport. #256's
projective slack-share method and vanishing-contraction barriers remain intact:
we count distinct normalized values, not a uniform fraction of a numerical gap,
and use denominators positive at the target rather than vanishing total target
slack. No general method for choosing universally small spectra is established.

## Reproduction and execution boundaries

    python3 scripts/test_projective_cube_spectra.py --out /tmp/projective-cubes

Eight cases d1,2,3,4,8,16,32,64 verify all original inequalities, exact active
labels, affine denominators, inverse identities, singleton facet witnesses,
common-row kernel formulas, whole support-line endpoints and target locks on130
original edges. There are260 facet witnesses. At d1..4 all98 full-row candidate
systems are solved independently, yielding30 actual vertices, and all33 eligible
orders are explicitly checked. Six forged controls fail. The saved consumer
replays without route production; large instances use the written formula and
structured kernel certificates, not full large graph/vertex enumeration.

The separate generic ratio-routing script also tests row-specific, non-common
normalizers, small positive minima and changing per-edge linearizations. The
full reports and fixtures are preserved and clean-replayed byte-for-byte.
Neither Python nor JSON decoding is kernel-verified. This note is an explicit
written proof, not a second Lean or platform theorem.
