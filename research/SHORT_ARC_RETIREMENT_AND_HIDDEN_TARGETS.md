# Short arcs preserve retired-face progress; no proper-face visibility guarantee

## What is new, and what was deliberately NOT duplicated

The first STATUS read still named #252's radius-two acquisition strategy. A
pre-write historical search found already-merged #253, which had independently
implemented COMPLETE two-face acquisition and a retired-face count. The duplicate
implementation prepared in this session was withheld. Neither that algorithm,
its product-of-polygons theorem, nor its binomial account is claimed new here.

This contribution uses #253's actual unchanged source (Git blob
`aa562f02dd492ecc47479381d637c6292757ebd3`). It proves and implements a
SAME-DECISION-ENDPOINT shortening: follow the shorter boundary arc to the same
certified fallback maximum, even if some intermediate edges decrease the phase
objective. It retains exactly the same permanent retired-face charges and
improves the resulting numerical upper bound. A new family has an arbitrarily
large actual shortening factor, while all decision endpoints stay identical.

A separate explicit family shows that increasing the dimension of incident
faces is not guaranteed to find a target-facet acquisition: in dimension d,
NO proper face at the source meets ANY target facet. The first acquisition
requires d edges, and the exact source-target distance is 2d-1. This is not a
Hirsch counterexample: the family has 3d genuine facets, so n-d=2d.

These are written mathematical arguments and executed rational checks, not
Lean-compiled or Prove2Me-accepted new statements. No proof admissions, target
skeletons, or speculative Actions runs are added. #250's projected-face line,
#244's core assembly, and all existing proof packets remain unchanged.

## 1. Preserve the maximum, shorten the way to it

Let P be a simple bounded full-dimensional d-polytope with m original facets.
Write e=m-d. At a decision vertex, the existing algorithm retains all acquired
target facets, explores every eligible incident two-face, and does one of:

* immediate or shortest polygon-boundary target acquisition;
* if none exists, a strictly phase-increasing polygon arc to a vertex z whose
  objective is maximal over ALL inspected faces.

A two-face F is a convex polygon. Exactly d-2 original facets contain it, and
each of its edges has a distinct additional original-row label. Thus its number
of edges is q(F)<=m-d+2=e+2. These are original edges, not projected chords or
auxiliary circuit moves. #253 provides the complete-cycle arithmetic auditor.

For a fallback, keep the EXACT vertex z chosen by the original rule, including
its original tie-breaking. Among all already inspected polygons containing z,
choose a shortest boundary arc from the current vertex x to z. In its selected
polygon there is an arc of length at most floor(q(F)/2). Therefore, with

    a=floor((e+2)/2),

every new fallback costs at most a original edges, replacing the older e+1
bound for a strictly increasing polygon prefix. Since the old increasing arc
is one available boundary arc, the replacement never uses more raw edges.
No additional face, vertex, LP, inverse, or neighboring-point discovery is needed.

Every fallback face was fully audited and is disjoint from EVERY then-missing
target facet: otherwise its intersection with that supporting hyperplane would
contain a polygon vertex, and the decision would have been an acquisition.
Consequently the shortcut cannot acquire a target facet prematurely, nor release
a previously locked facet. Its endpoint and the next decision are unchanged.
Inductively, ALL subsequent decision vertices, phase endpoints, phase objectives,
locked sets, and inspected faces are exactly those in the original run.

This is stronger than changing the greedy tie rule and hoping the new trajectory
is better. The complete reference certificate is retained and verified. Only the
paths BETWEEN its fixed decision anchors change.

## 2. The retired-face proof only needs anchor progress

In a fallback phase of intrinsic dimension h, an improving incident edge belongs
to h-1 distinct improving two-faces. The chosen maximum z dominates every
inspected face maximum. Hence none of those improving faces can be improving
at a later decision anchor in the same phase: its objective exceeds f(z).
After acquisition, each previously inspected fallback face is disjoint from
the newly locked target facet, and so cannot appear in later retained faces.

This argument compares DECISION ANCHORS, not intermediate path vertices.
The shortcut keeps all those anchors. It therefore preserves #253's entire
retired-face proof and its exact labels without requiring per-edge monotonicity.
Intermediate vertices may repeat or have decreasing objective. Chronological
loop erasure returns an original-edge path and cannot increase length. We do
NOT assert that the new loop-erased path must always be shorter than the old
loop-erased path; the guaranteed comparison is for raw committed walks.

Let r be the initial number of missing target facets. In a phase of dimension h,
labels consist of the fixed target rows plus h-2 non-target rows, giving at most
binom(e,h-2) distinct labels. As in #253,

    (h-1) B_h <= binom(e,h-2),  h>=3,

where B_h counts fallback decisions. There are no fallbacks at h<=2 and at most
one phase of each intrinsic dimension, because acquired target facets persist.
The shortcut therefore improves the derived committed-edge bound to

    L <= a * (r + sum_{h=3}^r floor(binom(e,h-2)/(h-1))).        (1)

It also verifies the run-specific bound

    L <= a * (number_of_acquisitions + number_of_fallbacks).    (2)

The previous integer bound charged e+1 per fallback; the new one charges a.
The difference can approach a factor of two in that term. Equation (1) is STILL
binomial/exponential when e and r grow together, not Polynomial Hirsch or a
new best general diameter bound. The unresolved cost is the number of distinct
retired labels, not whether one bad polygon arc is followed monotonically.

With fixed row labels the transformation is equivariant under invertible affine
coordinate changes and positive row rescalings: the old anchors and polygons
are equivariant, and shortest arc lengths and target-slack signature tie-breaks
are invariant. No invariance under arbitrary row-label permutations is claimed.

## 3. An arbitrarily large actual improvement, with identical anchors

Fix integers N>=8 and 1<=h<=N-2. Let Q be the polygon on the parabola (t,t^2)
with increasing parameter sequence

    0, 1/(h+1), ..., h/(h+1), 1,
    1+3/(2N), 1+6/(2N), ..., 5/2, 3.

Consecutive parameters a<b give facets (a+b)x-y<=ab; the closing facet is
-3x+y<=0. There are q=N+h+3 genuine polygon facets. Form Q x [0,1] in coordinates
(x,y,z), start at u=(1,1,0), and write w=(3,9,1) for the old top target vertex.

The normalized old target rows, each with slack one at u, are

    n0=(11/6,-1/3,0),  n1=(-3/2,1/2,0),  n2=(0,0,1).

Put F=n0+n1+n2. Add THREE cuts

    (F+ni).X <= (F+ni).w-epsilon_i,
    epsilon=(1/100,101/10000,51/5000).                       (3)

The new target v is the simultaneous intersection of (3). It is independent
of N,h and has exact coordinates

    v=(299507/100000, 28063/3125, 7979/8000).

In the old target's nonnegative slack coordinates s_i=ni.(w-X), the new cuts
are sum(s)+s_i>=epsilon_i. At v,

    sum(s)=303/40000,
    s=(97/40000,101/40000,105/40000)>0.

Thus v is strictly inside the three old target facets and lies exactly on the
three new target facets. It is feasible in every old inequality. For any
non-target lower polygon facet, its slack at w is (3-a)(3-b)>=1/4. Moving to v
changes that value by less than 1/20, so it remains strict, uniformly in N,h.

Every other old prism vertex satisfies every new cut STRICTLY. At the three
old neighbors of w this follows by direct substitution; a linear objective
strictly exposed at w attains its next-largest old vertex value at a neighbor,
or it would have an improving incident edge toward that value. Equivalently,
substitution along the two copies of the parabolic chain verifies it directly.
Consequently the cuts alter only the old vertex star, leaving every nonincident
old face untouched. All old facets remain genuine. Each new facet has a strict
relative-interior point obtained by slightly decreasing its other two cut
values near v. The tests verify these anchors against ALL original rows.

The resulting polytope is simple and has m=q+5=N+h+8 genuine original facets.
For simplicity inside the modified star: in three slack coordinates no feasible
vertex can have four active constraints. Two zero coordinates plus two new
rows would require equal epsilon values or one epsilon twice another; neither
occurs. One zero coordinate plus all three new rows contradicts s_i(v)>0.
Outside the star the original simple prism is unchanged.

### Same first fallback maximum, very different boundary routes

The phase objective automatically generated from the NEW target rows is

    f(X)=sum_i (F+ni).X/(4-epsilon_i).

Write it as ax+by+cz. Direct rational bounds give

    33/100<a<34/100, 16/100<b<17/100, 1<c<101/100.

It strictly increases along the parabolic parameter. The bottom-face maximum
is z0=(3,9,0), with gain 2a+8b>1.94 from u. The forward rectangular face through
u has maximum gain at most

    c + a*(3/16) + b*(2*(3/16)+(3/16)^2) < 1.15,

because N>=8. The backward rectangle has gain at most c<1.01. The three new
target cuts meet NONE of these initial faces. Therefore the original #253
fallback uniquely chooses z0 as the global inspected maximum.

Its permitted strictly increasing boundary prefix follows the whole forward
parabolic chain, costing N+1 edges. The new shortcut reaches exactly z0 by
walking BACKWARD h+1 edges to (0,0,0), then taking the closing polygon edge:
only h+2 edges. All h+1 backward steps decrease the old phase objective.

From z0, the upward edge first hits a new target facet. In slack coordinates
that point is (0,0,epsilon_1). Either eligible acquisition edge then reaches
a second new target facet, and the next edge reaches v. Thus both algorithms
use exactly THREE more edges, at exactly the same decision anchors. Hence

    original raw route: N+4,
    shortened raw route: h+5.                              (4)

The shortened route is shortest. Before entering a new cut, a route must reach
one of the three old neighbors of w: the bottom w-coordinate, the top parameter
0, or the top parameter5/2. Their original prism distances from u are respectively
h+2, h+2, and at least h+3. Deleting w cannot reduce those distances. The first
new facet therefore requires at least h+3 edges. It is the only new target
facet at that first simple entry vertex; acquiring the remaining two needs at
least two more ordinary edges. This proves the lower bound h+5 matching (4).

For fixed h, the ratio (N+4)/(h+5) is unbounded. This does not contradict the
factor-two improvement of the WORST-CASE numerical bound: a particular long
monotone polygon arc can be arbitrarily longer than the opposite short arc.
At N64,h2, the exact routes have68 versus7 edges on74 original facets. All77
inspected polygon-edge occurrences are counted separately from committed steps.
This is a bad route corrected by a shortest route, not a diameter counterexample.

## 4. A target invisible from EVERY proper face at the source

For each d>=2 set

    a_i=1/2+i/(10d^2),  c_i=d+a_i,  i=1,...,d,
    P_d={0<=x_i<=1, S+x_i<=c_i for all i},  S=sum_i x_i.

The source is u=0. Let S*=sum_i c_i/(d+1) and v_i=c_i-S*. Then 0<v_i<1 and
S(v)+v_i=c_i for every i. The d new rows are exactly the target facets. Source
and target have no common facet, so their smallest common face is P_d itself.

All 3d rows are genuine. On a lower/upper coordinate facet take that coordinate
0/1 and all others1/(10d); every other inequality is strict. On new row i, use

    v-eta*((1-e_i)-(d-1)/(d+1)*1),  eta=1/(100d^2).

The selected row stays tight, the other new rows gain slack eta, and the old
coordinate bounds stay strict. These are explicit relative-interior anchors.

If x_j=0 for ANY j, then S+x_i<=d<c_i for every i. Therefore no new target
facet meets any coordinate face x_j=0. Every proper face through u is contained
in at least one such coordinate facet: a supporting functional maximized at0
must have all coefficients nonpositive (small positive coordinate steps are
feasible); unless the face is all of P_d, some coefficient is negative and
its coordinate must remain zero. Thus

    NO proper incident face at u meets ANY target facet.    (5)

This excludes not only two-face acquisition but any fixed-dimensional or even
proper-face search at the initial source. It is not enough to increase the
searched dimension while continuing to assume an acquisition always appears.
The old #31 counterexamples concerned specified/selectable low-ridge facets and
particular two-face bridges. We do not claim that two-face failures were newly
discovered; (5), its all-dimensional family and exact distances are the distinct
claims here.

### Simplicity and the exact graph distance

At a point with a zero coordinate, all new rows are strict; a vertex there is
an ordinary cube vertex with d active coordinate rows. At a remaining vertex
only upper coordinate rows can be active. Let U index those rows and let F be
the free coordinates, |F|=m0. At most one new active row can also be indexed by U,
since two would imply distinct c_i values are equal. More than d active rows
would therefore force all new rows in F and one new row i in U to be tight.
Their sum then gives

    (m0+1)*a_i - sum_{j in F} a_j = 1.

But the left side is at most1/2+(m0+1)/(10d)<=3/5<1. Hence no vertex has more
than d active rows. Full dimension and the vertex rank condition give exactly
d independent rows: P_d is simple.

Before the FIRST target-facet acquisition, every visited vertex is an old cube
vertex, because no new row is tight. A first-hit edge retains d-1 old active
coordinate facets. Its new endpoint has all coordinates positive by (5), so
all those retained facets must be UPPER coordinate facets. Reaching its preceding
cube vertex needs d-1 coordinate flips from0, followed by the entry edge. Thus
first acquisition distance is at least d. At that first simple endpoint exactly
one target row is active; at least d-1 more edge steps are needed to acquire the
others. Every u-to-v route therefore has length at least2d-1.

An explicit matching route is as follows. First set coordinates2,...,d to1,
one at a time, keeping coordinate1 zero. Then move on the edge that releases
coordinate1's lower row, hitting target row2 at x_1=a_2. For k=2,...,d, define
z^(k) by

    S_k=c_k-1,
    z_j=c_j-S_k for 2<=j<k,
    z_j=1 for j>=k,
    z_1=(k-1)*a_k-sum_{j=2}^{k-1}a_j.

Its exact active set is new rows2,...,k plus upper rowsk,...,d. Every other row
is strict: monotonicity of a_i handles later new rows and the small perturbation
range handles coordinate1's remaining new row. Consecutive z^(k),z^(k+1) share
d-1 independent original rows and are distinct, hence are ordinary adjacent
vertices. z^(d) and v share new rows2,...,d, giving the final edge. The total is

    (d-1) + 1 + (d-2) + 1 = 2d-1.                         (6)

There is also a quantitative lower bound for face-based acquisition itself.
Before any target acquisition, a complete two-face disjoint from all target
facets is an unchanged cube square. Moving across it changes at most two of
the source zero coordinates. An incident two-face can meet a target facet only
once at most two zero coordinates remain, since any fixed lower coordinate
excludes every target facet by (5). Thus at least ceil((d-2)/2) fallback
DECISIONS are necessary before the first acquisition for a two-face-first rule.
For #253 in this family the phase objective has all positive coordinate
coefficients. While at least three zeros remain, its best inspected square
sets two zeros to one. It attains this fallback lower bound and reaches the
first target facet after exactly d ordinary edges. This is an all-dimensional
FIRST-PHASE statement; shortestness of its entire selector trajectory beyond
the tested dimensions is not inferred from it.

So (5) can coexist with a LINEAR shortest route and a d-edge first acquisition.
It is not an exponential diameter construction. A promising global argument
must allow controlled movement between incident faces, not demand an immediate
acquisition within one of them. This family is a regression target for that
claim, not evidence that polynomial phase bounds are impossible.

## 5. Executed evidence and remaining limitations

The wrapper verifies the exact unchanged #253 reference and all complete
original-row polygon witnesses, then audits shorter same-endpoint arc indices.
It does not rerun a solver inside validation. All previous retired-face counts
and original facet labels are retained, and (1)/(2) are checked on every output.
The generic assumptions remain simple, bounded, full-dimensional original-H
input; this is not a projected/nonsimple extension of #250's formal theorem.

The complete replay covers794 endpoint pairs on nine independently reconstructed
small original graphs. The original614-pair suite is UNCHANGED: both1230 total
edges, two nonshortest cases, shortest total1228. The three60-pair holdouts have
old605 versus596 edges, with five old versus four new nonshortest cases; shortest
sum592. One pair improves by nine edges; the other793 raw counts are unchanged.
No universal shortestness or loop-erased dominance is inferred from this sample.

Eight clipped-prism instances verify (4), including68->7 and68->21. Five small
independent graphs (two prisms and d2/3/4 hidden targets) verify all claimed
shortest/first-acquisition distances. The hidden family tests dimensions
2,3,4,5,6,8,12,24,48 with exact facet anchors and explicit2d-1-edge paths. Full
router runs occur only through d6; above that only the explicit path, bases and
separation identities are checked, not a full selector or complete graph.
The largest explicit path has95 certified original edges on144 facets.

Eighteen affine transforms,18 positive row rescalings,19 search-disabled audits
and12 rejected malformed/capped certificates are included. Producer/JSON is not
Lean-extracted. The existing two-face and original inverse auditors are reused
byte-for-byte, not quietly replaced by the withheld duplicate prototype.

Classical two-variable/simplex methods and bad pivot-rule examples already exist
(e.g. Yang arXiv:1910.10097; Disser--Mosis arXiv:2309.14034). We make no historical
novelty claim for polygon shortest paths, nonmonotone motion, or coordinate-cut
constructions. The contribution is the precise safe shortcut for this certified
retirement strategy, its improved count, and the explicit visibility/distance
family. Neither favorable experiments nor the still-binomial bound prove
Polynomial Hirsch. Bounding/compressing retired facet subsets remains open here.

    python3 scripts/test_short_arc_retirement.py
    python3 scripts/short_arc_retirement.py input.json --output route.json

The test writes full rational fixtures and raw reports. A completed generic
research proof is not reported as a Lean acceptance; no publication workflow
is requested for this code/note-only contribution.
