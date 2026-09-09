# Fixed-parent checkpoint rounding and simultaneous radial clipping

Continuation of PR #48 / PR #50, 2026-09-09.

## Status and scope

Polynomial Hirsch remains open. This continuation does not register new Open
Prove2Me children and does not assume `balanced_polynomial_bound`, circuit edge
refinement, or a polynomial bound for arbitrary repair faces.

The seven declarations in `Solutions/PolynomialFacePreservingCheckpoints.lean`
are kernel-verified at commit `bbfdaf391d559e38f23c858caa170c700bf424d5`, Actions
run `34402183035`, job `102636479097`. The audit checked 30 reports and found
only `propext`, `Classical.choice`, and `Quot.sound`.

`Solutions/PolynomialRadialClipCells.lean` isolates the algebra of the actual
geometric construction below. Its verification must be read from the branch's
latest workflow, not inferred from the earlier seven-theorem run.

The **complete simultaneous-clipping theorem below has an ordinary mathematical
proof and an exact executable certificate constructor, but is not yet assembled
as one end-to-end Lean theorem**. The finite breakpoint/face-cover extraction
and the clipped-old-edge budget remain formalization work, not assumed global
geometric conjectures. No Prove2Me ACCEPTED verdict is claimed for this branch.
No novelty claim relative to the literature is made.

## 1. The intermediate-vertex requirement is removable

Let P be compact, and let F_i be any family of closed extreme subsets of P.
For every x in P, there is a vertex r(x) of P such that

    x in F_i  =>  r(x) in F_i, for every i simultaneously.

Moreover, choose r(v)=v for every existing vertex v. The family need not be
finite. This is NOT a continuous or nearest-vertex map, and it need not preserve
edges or lengths.

Proof: intersect P with all F_i containing x. That intersection is nonempty,
closed, compact, and extreme in P. The Krein-Milman lemma supplies an extreme
point of the intersection, which is also extreme in P. Select such a point,
except that an input which is already a vertex is left unchanged.

Consequences proved in Lean:

* An ordinary shared point of two closed parent faces supplies a shared parent
  vertex; the original shared point need not be a vertex.
* A fixed feasible face-covered checkpoint sequence with vertex endpoints can
  be rounded simultaneously without changing its available face budget.
* PR #48's start/active-containment theorems need only vertex endpoints of the
  entire route, not vertex endpoints of every marked interval. For the start
  version, unmarked interior checkpoints need not even be feasible.

The result is geometric: it uses compactness and actual extreme faces. Merely
preserving labels of faces of an earlier, different polytope does not suffice.

## 2. A genuine single-facet sweep defeats naive label transport

Take

    P_t = [0,1]^3 intersect {3x + 2y + z <= t}

and move the last facet from t=11/2 to t=9/2. Both endpoint polytopes are simple,
full-dimensional and irredundantly represented by the same seven inequalities;
both have ten vertices. Only one old cube vertex value, 5 at (1,1,0), lies
strictly between the two levels, so this is a genuine local polytopal sweep,
not an abstract crossing-interval fabrication.

The stationary faces F_x={x=1} and F_y={y=1} intersect in P_(11/2), but are
DISJOINT in P_(9/2): their simultaneous equalities force 3x+2y+z >= 5.
Each face separately remains a genuine final facet.

There is even an old shortest path with surviving endpoint vertices:

    u=(1,0,0) -> z=(1,1,0) -> v=(0,1,0).

Its first edge lies in F_x and its second in F_y. The shared checkpoint z is
removed. In the final parent, the network consisting only of those two support
faces has a closed separating cut. The ambient polytope is not disconnected:
its u-v distance is still two, through (0,0,0).

The FINAL moving facet M={3x+2y+z=9/2} provides genuine missing connectors:
F_x intersects M and M intersects F_y. For example,

    u, (1,1/2,1/2), (2/3,1,1/2), v

is a feasible face-covered sequence supported by F_x, M, F_y, although its two
interior checkpoints are nonvertices. The new Lean rounding theorem applies.

The radial constructor in section 3 obtains an actual three-edge final route
from the damaged old two-edge path. Its certified bound is 2+diam(M)=4. This
bound need not be sharp; the true final distance is two.

A smaller, five-facet intersection-loss witness is the tetrahedron

    x,y,z >= 0, x+y+z <= 1, 3x+2y+z <= t,

with t=5/2 and t=3/2. Both endpoint descriptions are simple and irredundant,
but the two stationary facets z=0 and x+y+z=1 lose their intersection. This
smaller example is not asserted to have the stronger old-geodesic property.

These witnesses refute automatic transport of earlier face intersections into
the final parent. They do NOT refute existence of a better repair network, do
not impose every Dantzig-specific hypothesis, and do not refute Polynomial
Hirsch. The final-cut connector is precisely a weaker condition that survives.

## 3. Positive geometric construction: simultaneous monotone clipping

### Precise theorem, with its limitations

Let Q be a convex polyhedron, and let

    P = Q intersect intersection_i {a_i(x) <= b_i},   i=1,...,m,

be compact. Assume there is o in Q with a_i(o)<b_i for every added cut.
Let u,v be vertices of P which are also vertices of Q. Suppose an L-step
edge/stay walk in Q joins u to v. For the FINAL cut faces

    F_i = P intersect {a_i(x)=b_i},

assume intrinsic graph diameter at most B_i. Then there is a P-edge/stay route
from u to v of length at most

    L + sum_i B_i.

More precisely, the construction supplies a connected fixed-parent repair
family consisting of at most m final cut faces and at most L clipped old
edges. Every distinct support is charged once, irrespective of the number
of intermediate facet-translation events or repeated visits.

This is a theorem about surviving endpoints and a given OUTER EDGE walk.
It is not an unrestricted diameter bound for arbitrary newly created vertices,
not a theorem about an arbitrary circuit walk, and not a theorem about every
non-nested/projectively changing sequence. Every B_i remains an explicit cost.

### Construction and proof

Set s_i=b_i-a_i(o)>0. For x in Q, define

    lambda_i(x) = (a_i(x)-a_i(o))/s_i,
    mu(x) = max(1, lambda_1(x), ..., lambda_m(x)),
    rho(x) = o + (x-o)/mu(x).

1. mu>=1. Hence rho(x) is a convex combination of o and x and stays in Q.
   Also lambda_i<=mu implies a_i(rho(x))<=b_i for every i. Thus rho maps Q
   into P. It fixes every point of P, including u and v.

2. If mu(x)>1, an added cut attains the maximum. For that index i,
   a_i(rho(x))=b_i: rho(x) lies in the FINAL face F_i. This statement refers
   to fixed final inequalities, never to a face of an intermediate polytope.

3. Parameterize one old edge by x(t)=(1-t)p+tq, 0<=t<=1. Each lambda_i(x(t))
   is affine in t. Include the constant affine function 1. Insert 0, 1, and
   all intersections inside (0,1) of pairs of distinct affine functions.
   This is a finite partition with at most binomial(m+1,2)+1 cells per old
   edge. Identical affine functions create no additional breakpoint.

4. In each closed cell, one affine function is maximal throughout. A maximizer
   at an interior point stays maximal at both ends and throughout the cell:
   otherwise an affine difference would have a zero in the cell's interior,
   which was already inserted as a breakpoint. Ties at endpoints are harmless.
   The exact checker additionally verifies all endpoint dominance inequalities;
   affine interpolation then certifies the whole cell, not just samples.

5. If the constant 1 is the chosen maximizer, rho(x(t))=x(t) throughout that
   cell and its image lies in E intersect P, where E is the old edge. Otherwise
   its entire image lies in one fixed F_i. Consecutive cells share rho(x(t))
   at their common breakpoint. Consecutive old edges likewise share the SAME
   rho at their common old vertex. The entire resulting checkpoint sequence
   is therefore feasible and genuinely face-covered in ONE fixed parent P.

6. E intersect P is a closed extreme face of P: any open segment in P hitting
   it has its endpoints in E because E is extreme in Q and P is a subset of Q.
   It is a compact convex subset of a segment, so it is empty, a point, or a
   segment. Its intrinsic graph diameter is at most one. The F_i are closed
   exposed faces of P; any nonempty one is proper because o is strictly feasible.

7. Apply simultaneous face-preserving rounding from section 1 to the finite
   checkpoint sequence. All parent-face memberships and both endpoints are
   preserved, even though radial images of old vertices can be nonvertices.
   Existing distinct-region routing then charges each available final cut
   face once and each distinct clipped old edge at most once.

8. There are at most L distinct old edges and at most m final cut labels, so
   the total budget is L+sum_i B_i. Stay steps can simply be deleted first;
   zero-length paths use a constant route. The m=0 case is the identity map.

This gives a concrete, falsifiable answer to part of the PR #48 representation
question for MONOTONE CLIPPING: do not preserve each historical checkpoint's
old face labels. Retract the entire old path into the final parent and add the
final cut faces. The number of Pachner events is not the relevant charge.
The single-cut special case overlaps the existing clipping toolkit; the
simultaneous final-face charge is the useful amortized formulation here.

### What is still not a polynomial proof

A polynomial number of support faces does NOT imply polynomial total cost.
The B_i can still encode the difficult lower-dimensional routing problem.
Repeated dimension reduction with uncontrolled retained row counts can give
exponential or quasipolynomial recurrences, not a fixed polynomial. Do not
assume effective row count <= twice the face dimension.

Nor can the old L circuit steps be charged as L clipped edges: a circuit
segment need not be an extreme face of the outer polytope. Establishing an
appropriate inexpensive outer-edge model, or a separate direct application
to the prescribed-face leaf, remains substantive geometry.

## 4. Actual circuit obstruction to the tempting shortcut

The irredundant hexagon

    |x|+|y| <= 2,  |y| <= 1

has a maximal horizontal row-circuit step from (-2,0) to (2,0). The horizontal
row-zero normals span dimension d-1=1, certifying circuit minimal support.
The maximal step length along (1,0) is exactly 4. The endpoints have graph
distance three, share no tight row, and their midpoint is strictly interior.
Consequently NO proper face of this polytope contains the entire step.

Rounding the two endpoints does nothing; they are already vertices. Including
the whole polytope as a repair support would put its unknown diameter directly
into the cost. That would not solve circuit-to-edge refinement and must not
be disguised as a smaller Prove2Me child.

## 5. Exact regression suite

Run `python3 scripts/test_face_preserving_checkpoints.py` (standard library).

The suite exhaustively enumerates candidate vertex bases over rational numbers,
reconstructs edge adjacency from common tight-row rank, computes all needed
face diameters by BFS, and explicitly constructs the final repaired walks.
The examples are bounded/full-dimensional cubes, clipped cubes, a tetrahedron,
a hexagon, and polars of the existing exact 4D/5D Dantzig witnesses.

Results at creation:

* Simultaneous rounding: 1,506 checkpoints across 2D/3D/4D cubes and the 4D/5D
  Dantzig regressions, including every nonempty face barycentre and rational
  vertex-pair mixtures. The Dantzig polars have 14 and 40 vertices respectively.
* Radial multi-cut construction: 48 seeded cases in dimensions 2, 3, 4, with
  zero through three added cuts, repeated old edges, and possibly redundant
  cuts. All 694 affine cells are certified at both endpoints. There are 196
  nonvertex checkpoint occurrences. Every constructed route meets the stated
  final-face budget; at most ten distinct supports occur in a case.
* The actual seven-facet sweep, the five-facet intersection-loss example, and
  the six-row maximal-circuit/proper-carrier obstruction are checked exactly.

Random test generation is not a proof of the general theorem. The saved
`research/checkpoint_regression.json` records the exact deterministic run.
The general algebra, geometric selector, and routing implications are separate
Lean declarations; the complete cell enumeration is still an executable
rational certificate constructor plus the general proof in section 3.

### Sources and provenance

* PR #48 supplies the start/active-containment routing source; PR #49 published
  the original start-containment result on Prove2Me.
* Pinned Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`,
  `Mathlib/Analysis/Convex/KreinMilman.lean` and `Extreme.lean`, supplies the
  compact extreme-point existence and extreme-set transfer facts.
* Dantzig coordinates are copied exactly from `research/TwoFaceBridgeCounterexample.md`
  and `research/SelectableTwoFaceBridgeCounterexampleD5.md` at repository commit
  `4b09066a5e7a68e664790d56f4e11d24cf9475ee`. The 5D integer coordinates are
  uniformly rescaled, then centred before taking the polar; neither operation
  changes the cited combinatorial type.
* The historical discussion describes translating a hyperplane along its normal
  and separately warns that a gradually changing path is not a fixed certificate:
  https://gilkalai.wordpress.com/2009/08/09/the-polynomial-hirsch-conjecture-discussion-thread/
  comments 85, 101, 102 and 104. Its unproved historical global claims are NOT
  assumptions in this continuation.

## 6. Next precise work, without a cyclic decomposition

Assemble the finite affine-cell extraction and clipped-segment diameter-one
lemma into a single Lean theorem with section 3's exact hypotheses. Then check
which projective-removal normalization supplies a common-coordinate outer
edge route with surviving endpoints. Only after those hypotheses are actually
met should the remaining final-face charging problem be linked to the existing
common-face/effective-row/ordered-tail results.

For a genuine fixed-parent feasible trace, vertex portals are now automatic.
For a monotone clipping model, the radial construction avoids historical-label
transport and gives polynomial support COUNT. The hard unresolved quantitative
question is still total face COST, together with the applicability of this
model to the desired global reduction. Do not reopen completed Santos or
cubic-circuit work, and do not publish a child equivalent to the ancestor.
