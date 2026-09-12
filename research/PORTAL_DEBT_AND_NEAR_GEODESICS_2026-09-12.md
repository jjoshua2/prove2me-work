# Cross-level portal debt and the cost of insisting on shortest region paths

## Status and what changes after #206

This continuation is based on main `321f473d871aad2d692595acd97a667d6a648d06`.
It leaves #205 and #206 untouched. Its three Lean modules use only already
merged imports, not the uncompiled #206 candidates. No new Lean compilation,
axiom audit, hosted gate, or Prove2Me acceptance is claimed. The exact Python
checks were executed; the receipts distinguish them from kernel verification.

There are three mathematical results:

1. In a **simple** polytope, an all-facet geodesic with chosen vertex portals
   has exact child-dimension mass `h + number of visited neutral facets`, hence
   at most `m-h`, where h,m describe the intrinsic parent. Recursing gives an
   exact additive ledger: final edge count equals initial carrier dimension
   plus the sum of these neutral-facet charges over ALL internal nodes.
2. A concrete infinite family shows that even perfect portal optimization
   subject to a metric-shortest top-level facet path can be arbitrarily bad
   compared with actual graph distance. With `10+2k` facets and `16+4k` vertices,
   its best such repair costs `6+2k`; a five-edge route always exists and is
   shortest. One additional region edge permits that route. This does not
   refute any polynomial diameter bound: the bad repair is linear in m.
3. The #206 contact-window proof tolerates additive region-path slack q:
   each available label contacts at most q+3 path positions. Its same
   disjoint-row budget therefore gives `sum(delta)+r*s <= r*e+(q+3)*s`.
   At full availability s=e, q=1 retains the linear resource bound `4e`.

The first result concerns ALL intrinsic facets and simple polytopes. The third
applies to the mixed clipping graph and does not require simplicity. They are
related tools, not identical certificates or a silent relaxation of #206's
stored `shortest` field. The end-to-end near-geodesic clipping wrapper remains
to be formalized; the old callback only needs selected-pair routes and no
repeated old-edge labels. A path with one extra edge is still simple, since a
repeated vertex would remove a cycle of length at least two and contradict the
allowed slack. The generic proof also counts positions, so it does not hide a
nodup assumption for larger slack.

## 1. Exact intrinsic-dimension accounting at a portal chain

Let F be a bounded simple h-polytope with m genuine facets, and let u,v be
vertices whose smallest common face is F. Thus u and v share no intrinsic
facet. Every vertex of F lies on exactly h facets. For vertices x,y, write
I(x) for their intrinsic active-facet set. Simplicity gives

    dim(commonFace(x,y)) = h - |I(x) intersect I(y)|
                         = |I(y) minus I(x)|.                 (1)

This uses genuine irredundant facets, not an arbitrary padded row list. A
common face of a simple polytope remains simple. Restricting a parent facet to
such a face either gives the whole face, no intersection, or one intrinsic
facet. Distinct surviving parent facets give distinct intrinsic facets. At a
vertex this follows from the local Boolean face lattice of its simplicial
normal cone: common active facets are fixed and each extra active facet cuts
codimension one. Hence original facet identities can be retained through the
whole recursion.

Form the intersection graph of every intrinsic facet, augmented by the two
endpoint singleton regions. Two labels are adjacent when the regions share a
vertex. Pick a metric-shortest path

    {u}, F_1,...,F_r,{v}.

For each consecutive pair choose a shared vertex. These portals are
`z_0=u,z_1,...,z_r=v`. Child i is the smallest common face of z_(i-1),z_i and
is contained in F_i. Its dimension is strictly less than h. Coincident portals
produce a zero-dimensional child, not a paid edge.

### A sharper consequence than the three-label window

If a facet G is active at portal z_a, G contacts BOTH region positions a and
a+1. If it is also active at z_b with b>=a, it contacts position b+1. The
usual two-edge shortcut through G implies `(b+1)-a <= 2`, so

    b-a <= 1.                                                (2)

Thus G is active at at most two consecutive portals. In particular it cannot
be dropped and re-entered in this coarse portal sequence. Labels equal to G
are counted as closed-neighborhood contacts; they do not require a graph loop.

Let V be the union of the active sets at all portals. Since no facet re-enters,
each facet not active at u is entered exactly once if it is ever seen. Using
(1),

    sum_i dim(C_i) = |V|-h.                                  (3)

Let N consist of facets active at some portal but at neither u nor v. The
endpoint active sets are disjoint and have h elements each, so

    |V|=2h+|N|,
    sum_i dim(C_i)=h+|N| <= m-h.                             (4)

This is an equality involving the SAME chosen portals, not an estimate obtained
by changing a path after selecting costs. It is sharper for dimension mass than
simply charging every available row three times, but it has different hypotheses
and does not replace #206's nonsimple mixed-graph excess theorem.

More generally, for equal-rank endpoint signatures that may overlap, replace h
on the right side of (4) by `|I(v) minus I(u)|`, the common-carrier dimension.
The finite-set core only needs the history condition: every element in the next
signature that was seen earlier must still belong to the current signature.
`PolynomialPortalSignatureMass.lean` formalizes the fresh-chain union telescope,
its split into endpoint entries and neutral labels, and the resulting excess
bound. It does not yet formalize the entire intrinsic simple-polytope interface.

## 2. A cross-level invariant, not a repeated dimension upper bound

Recursively apply the construction inside each proper child carrier, stopping
at equal points or ordinary edges. The recursion terminates by dimension.
An edge of an extreme face is an edge of every ancestor polytope; concatenating
the leaves gives a genuine ordinary-edge walk.

For a node t, let h_t be its endpoint carrier dimension and nu_t the number of
its newly visited neutral facets. Equation (4) says

    sum(child h) = h_t + nu_t.

Telescoping over the FINITE recursion tree gives

    number of edge leaves = h_root + sum_internal_nodes nu_t. (5)

Zero-dimensional leaves contribute zero. There is no multiplication by depth,
branch count, or carrier excess. But there is also NO assumption that a neutral
facet charged in one child cannot be charged again in a different child.
Every occurrence is retained.

### Row-by-row interpretation

For each ORIGINAL facet j, record its zero/one tightness along the final edge
walk. Let T_j be its number of bit changes and let b_j be one if its endpoint
bits differ, zero otherwise. Then

    T_j = b_j + 2*c_j,                                      (6)

where c_j is exactly how often that facet was charged as neutral somewhere in
the recursive portal construction. Each ordinary edge changes two active
facets in a simple polytope, so summing (6) is also a direct proof of (5).

The charge is an extra on/off cycle, not necessarily a literal re-entry into
a facet that was present at the root source. If a row is absent at both root
endpoints, even its first intervening visit contributes a cycle. A source facet
may contribute only if it returns after being left. A facet shared by the root
endpoints remains fixed inside the smallest common face and contributes zero.

For arbitrary (non-geodesic) portal chains, the same ledger remains exact when
local charge counts these cycles, rather than just distinct neutral labels.
An element may then be charged more than once or have been active at a node
endpoint. The generic triangle-gap formulation is

    entries(u,z)+entries(z,v)-entries(u,v),

where entries(x,y)=|I(y) minus I(x)|. The directed set metric satisfies the
triangle inequality, so this is a nonnegative integer.
`PolynomialRecursivePortalDebt.lean` formalizes finite edge trees, constructs
their actual relation routes, and proves length = endpoint entries + total debt.
Its edge input is "one new facet enters across an edge", not a local diameter
oracle. The simple-polytope application is established in this note and in the
exact geometric checker, not by claiming those interface facts have already
been Lean-compiled.

### Why this is a useful but incomplete potential

If a geometric selection rule established total debt <=B, (5) would give the
actual route bound h_root+B. The question is now to control a specific source
of extra steps, not all carrier sizes independently. However, total debt has
NOT been proved polynomial for arbitrary inputs or for the tested selection
rules. Merely defining or measuring it is not a solution to Polynomial Hirsch.

An exact six-dimensional Dantzig example in the packet has 12 facets and 84
vertices. Opposite endpoints share no facet and cover all facets, so the root
has NO neutral facets and root debt zero. A frozen lexicographic choice still
pays one unit in descendants and gives seven edges. Optimizing descendant
choices gives six. Zero debt at the root is therefore not enough for a global
nonrevisiting route. This example is not a Hirsch counterexample.

## 3. A ten-facet exact obstruction to strict facet-geodesic routing

In R^3 take these inequalities, numbered 0 through 9:

    0: -x <= 0             5: z <= 3/4
    1: -y <= 0             6: x+2y <= 5/4
    2: -z <= 0             7: -x-y-z <= -1/4
    3: x+y+z <= 1          8: -x-y+z <= 5/8
    4: y <= 1/2            9: x <= 7/8.

This is a bounded simple polytope with ten genuine facets and sixteen vertices.
The fixed input supplies a strict interior point and a strictly positive normal
balance. Full exact active-basis enumeration checks the entire vertex list,
facet irredundancy and simplicity, not a supplied partial graph.

For a constructive completeness check, start from the tetrahedron given by
rows 0--3 and add rows 4--9 in that order. They truncate, respectively, the
single vertices `(0,1,0)`, `(0,0,1)`, `(1/2,1/2,0)`, `(0,0,0)`,
`(0,0,3/4)`, and `(1,0,0)`. Each new level is strictly between that vertex's
unique maximal row evaluation and the next largest evaluation. Six simple
vertex truncations therefore give precisely ten facets and sixteen vertices,
independently of the subsequent active-basis enumeration.

Choose

    u=(1/8,0,3/4),          I(u)={1,5,8},
    v=(1/4,1/2,0),          I(v)={2,4,6}.

The only intersecting pair consisting of a source facet and a target facet is
F_1,F_2. This can be seen directly: F_1 cannot meet F_4 because their y values
conflict, or F_6 because it would force x=5/4>7/8. F_5 has z=3/4, making every
target facet incompatible with nonnegativity and x+y+z<=1. On F_8,
z=x+y+5/8 and x+y<=3/16; all three target facet equations are impossible.

F_1 intersect F_2 is the edge with endpoints

    a=(1/4,0,0),           b=(7/8,0,0).

Consequently every metric-shortest facet path is exactly
`{u},F_1,F_2,{v}` and its portal must be a or b. Both F_1 and F_2 are heptagons.
Inside F_1, u is three graph steps from EACH endpoint a,b. Inside F_2, v is
also three steps from each. Thus even an oracle giving true shortest child
routes must pay

    min_z [dist_F1(u,z)+dist_F2(z,v)] = 6.                   (7)

This is stronger than showing one bad portal choice: BOTH possible portals,
and the only possible shortest facet-label path, have been exhausted.

There is instead the five-edge ordinary route

    (1/8,0,3/4), (0,0,5/8), (0,0,1/4),
    (0,1/4,0), (0,1/2,0), (1/4,1/2,0).

Each consecutive pair shares exactly two independent defining facets.
The route has region cover `{u},F_1,F_0,F_2,{v}`: ONE extra region edge.
There is no path of length four. For a short reproducible lower-bound
certificate, the radius-two active-signature sets are

    from u: 158; 018,058,135; 017,035,139,
    from v: 246; 024,346,236; 027,034,239.

They are disjoint. Simplicity means each triple names a unique vertex and an
edge replaces one facet, so a path of at most four would put some vertex in
both balls. The exact checker independently recomputes these distances.

The strict-geodesic repair via a charges facet 0 in BOTH child polygons;
its total debt is three, versus two for the five-edge relaxed route. Three-
position contact windows at individual nodes therefore do not imply that the
same original row is charged just once across different descendants.

## 4. An infinite family with unbounded relative overhead

The example admits a controlled amplification. In each round truncate both
endpoints of the current edge F_1 intersect F_2, using planes sufficiently close
to those vertices that no other old vertex is removed. A precise rational
choice is the sum of the three active normals at the selected vertex, cut at
the midpoint between its unique maximum and the second-largest old-vertex
value. This replaces one simple vertex by three edge intersections, preserves
simplicity, and adds one facet. Do this at both endpoints in each round.

After k rounds:

    dimension=3,  facets=10+2k,  vertices=16+4k.             (8)

The source, destination, and all five-route vertices survive. Every old edge
in that route survives because neither endpoint is truncated. The original
source and target active sets remain unchanged. Intersections of old facets
can only shrink, and the shared F_1/F_2 edge remains nonempty. Thus the ONLY
shortest source-facet/target-facet pair is still F_1,F_2.

In each heptagonal facet, truncating each shared-edge endpoint adds one vertex
on each of the two arcs from the chosen endpoint to that edge. Therefore both
local distances to either current shared-edge endpoint increase by exactly
one per round. The cost of EVERY strict shortest-facet-path repair is

    (3+k)+(3+k)=6+2k.                                      (9)

The actual distance is still exactly five. The unchanged route proves <=5.
Conversely, collapsing the three replacement vertices at a truncation back
to the removed vertex is a graph homomorphism if stationary steps are allowed:
new edges either map to old edges or collapse. Thus truncation cannot shorten
the distance between retained old vertices. Apply the base lower bound five.

The five-edge route still has the same one-extra-region-edge cover. Hence
allowing one extra region edge changes the optimum from 6+2k to 5, an unbounded
approximation ratio as k grows. This is NOT an exponential diameter example
and NOT a disproof of polynomial bounds for strict-geodesic repairs: 6+2k is
linear in the number of facets. It is a precise obstruction to treating the
shortest facet skeleton as a harmless or cost-optimal restriction.

The largest executed example has k=20: 50 facets, 96 vertices, strict cost 46,
relaxed cost five. Its root local debt remains ONE, while the total strict
recursive debt rises to 43. Immediate portal dimension minimization therefore
also misses the accumulation that matters.

## 5. One extra region edge preserves a linear all-row resource bound

Let p have L edges with `L <= dist(start,end)+q`. If a graph vertex z contacts
positions r<=s, splice in the two-edge walk through z. Then

    dist(start,end) <= r+2+L-s,
    L <= r+2+L-s+q,
    s-r <= q+2.                                           (10)

Thus z contacts at most q+3 positions. This is sharp for each q: take a path
of q+2 edges and a vertex adjacent to all its q+3 vertices. The original
endpoints have graph distance two.

For actual portal activity the two-sided contact argument instead gives
`b-a<=q+1`. At q=0 it yields nonreentry and the neutral-label identity above;
at q=1 it allows new patterns, so the triangle-gap/cycle ledger must be used.
Do NOT continue to equate local debt with only distinct neutral labels after
relaxing geodesicity.

For the #206 mixed graph, keep the SAME geometric pointwise row-saving input

    delta_i+s <= e+t_i.

Double-counting (10) over the selected occurrences gives

    sum(delta_i)+r*s <= r*e+(q+3)*s.                        (11)

At s=e, q=1, this is `sum(delta_i)<=4e`, replacing 3e but remaining linear.
Combined with the known h_i<=delta_i and M_i<=2delta_i, it also gives intrinsic
size sums <=4e and <=8e. If actual carrier dimensions are <=H, the mathematical
Larman consequence is `D+8e*2^max(H-3,0)`, compared with D+6e times that factor
for strict geodesics. The dimension cap is NOT asserted for arbitrary inputs.

`PolynomialNearGeodesicWindows.lean` proves the span, position count, finite
load sum, subtraction-free mass implication, and q=1 specialization. It
consumes the pointwise geometric resource inequality, not an edge-distance
assumption. A near-geodesic counterpart of the concrete deferred clipping
structure needs a separate adapter; this PR does not modify its `shortest`
field or claim that adapter was compiled.

## 6. The executable oracle and what the measurements show

`portal_debt_router.py` accepts rational inequalities, a strict interior point,
and a positive normal balance. It enumerates ALL candidate vertex bases and
checks feasibility, simplicity and genuine facets. It then computes four
finite strategies:

* lex: choose the first shortest facet path and first portal vertices;
* local: minimize immediate child-dimension mass across all shortest facet
  paths and portals, but ignore future debt when choosing;
* recursive: optimize all descendant costs over all shortest facet paths;
* relaxed: optimize recursively with at most one extra region edge per node.

The recursion is on proper common-face dimension. Portal optimization uses
layered dynamic programming with exact integer costs. The router does NOT
consult ambient graph distances. Independent test code computes those by BFS
only to compare the returned routes with the true optimum. The barrier lower
bound also computes true graph distances INSIDE the two facets, independently
of the router, so it does not merely trust that the optimizer found its best.

This is an exponential RESEARCH ORACLE, not a polynomial algorithm: full vertex
lists can be exponential, as can the number of face/pair states. It exists to
falsify bad geometric hypotheses and test new rules while retaining exact edge
and row identities.

Across 19 base models and 1,916 endpoint pairs, recursive optimization improves
273 lexicographic routes and 140 locally optimized routes. It still exceeds the
true distance for 13 pairs. One-extra-edge optimization reaches the true distance
for those 13 and for every tested pair. That finite observation is NOT a theorem
that one extra region edge always suffices, or that this selection rule has
polynomial diameter/runtime.

The main audit checks 7,672 ordinary route certificates including two additional
fixed examples. The amplified family adds 14 certificates in seven sizes.
All 1,099 labeled graphs through five vertices provide 40,307 simple paths
within one edge of geodesic distance and 200,273 contact-window checks. The
finite-set audit checks 1,809 signature chains, including 417 nonreentering
chains. Sixteen malformed or forged cases are rejected, notably an undeclared
slack-one path offered as a geodesic and a nonsimple pyramid offered as simple.
Receipts bind the actual executed source hashes.

## 7. Existing literature and the next mathematical target

Recursive facet/link routes are a classical subject, not a new category of
proof. Labbé, Manneville and Santos, *Hirsch polytopes with exponentially long
combinatorial segments*, arXiv:1510.07678, Theorem E, construct Hirsch polytopes
on which all monotone-conservative combinatorial segments between certain
facets are exponentially long. Their procedure is not identified with this
exact all-facet portal optimizer, so their lower bound must NOT be copied over
to it without an equivalence proof. The result is a serious warning against
inferring a polynomial bound from a nested shortest-path construction alone.

Primary source read in this continuation:
https://arxiv.org/html/1510.07678 (especially the introduction and Theorem E).
No claim of a newly best classical diameter bound or a globally new invariance
principle is made here. The additions are the repository's precise portal-debt
accounting, an exact small/infinite counterexample to a natural restriction,
and the quantitatively safe near-geodesic relaxation.

The next target is a portal-selection rule that bounds total excursion debt,
using controlled detours to avoid charging the same row in overlapping child
repairs. The proof must bound cumulative debt, not just root neutral count,
local rank, or skeleton length. The new family is a mandatory test: an acceptable
cost-sensitive strategy should take its five-edge bypass rather than 6+2k.
A universal polynomial bound on the debt or on required detour slack remains
unproved by this work. No new open platform child or cosmetic root dependency
is added.
