# Mixed-defect absorption and bounded refinement macros

## Status and relation to the live frontier

This is written mathematical research and exact Python, NOT a Lean compilation,
axiom audit, or Prove2Me acceptance. It does not solve Polynomial Hirsch. It
extends the exact stellar update and original-edge carrier machinery of merged
#261; none of those older sources is modified. Original input polytopes are
simple, bounded, full-dimensional, with genuine original facet rows. A small
number of defects, a successful bounded macro, or a cheap residual refinement
is not silently assumed for arbitrary polytopes.

The new step is to allow UNEQUAL higher-defect incidences when all would-be
extra descendants have explicit smaller blockers. It gives an exact descending
integer potential. A separate, tightly audited macro rule may cross a neutral
or increasing step only when its whole bounded sequence decreases the potential.
A rational five-dimensional plateau demonstrates why that distinction matters.

## 1. Exact absorption criterion

Let N(K) be the minimal nonfaces of a simplicial complex K, and H(K) those with
at least three labels. In the dual of the original polytope, these are minimal
empty intersections of original facets. Define

    W(K) = sum_{N in H(K)} (|N|-2).

The #261 membership proof gives the complete minimal-nonface update when a FACE
edge E={u,v} is stellar-subdivided with a new label z: take the inclusion-minimal
members of

    {E},
    {N in N(K): E is not contained in N},
    {{z} union (N minus E): N in N(K), N intersects E}.             (1)

An arbitrary such move can increase W. In particular, the mixed edge of a join
of two triangle boundaries creates two additional higher nonfaces. We never
use an unconditional potential-monotonicity assertion.

Call a high defect SHARED if it contains E and MIXED if it contains exactly one
endpoint of E. Require at least one shared high defect. For EVERY mixed high
N, supply a minimal nonface B satisfying

    B contains E, OR B is a missing pair meeting E;
    B minus E is contained in N minus E.                            (2)

Then the would-be mixed descendant z+(N-E) contains the smaller generated
nonface z+(B-E), so it is not a new minimal high defect. This is a finite,
individually checkable absorption witness, not an assertion about matching
incidence signatures.

### Exact theorem

Under (2), the full new higher-defect family is exactly

    {N in H(K): E not contained in N}
      union {z+(N-E): N in H(K), E contained in N, |N|>=4}.          (3)

Shared triples become missing pairs. All other high defects persist. If c_E is
the number of shared high defects, then

    W(K') = W(K)-c_E,                 c_E>=1.                      (4)

To verify the exactness, first every mixed descendant is excluded by its
witness (2); descendants of old missing pairs have size two. An old high N not
containing E cannot lose minimality: an old smaller nonface would contradict
its original minimality, E is not inside it, and a new z-containing nonface
cannot lie inside an old vertex set. A shared descendant z+(N-E) cannot be
swallowed by an old nonface inside N-E, nor by another descendant z+(B-E): either
would imply a proper old nonface B inside N. It cannot contain the new pair E,
whose endpoints it lacks. Shared descendants are distinct, so counting their
size reductions proves (4).

Equal nonempty higher incidence, #261's safe case, is a special case with no
mixed defects at all. The new rule is strictly stronger. For example high
nonfaces 0123 and 0234 admit E=01. The shared descendant z23 absorbs mixed
z234, while the old mixed nonface 0234 stays. W drops from four to three.
This example needs a SHARED HIGH blocker, not just a pre-existing missing pair.

## 2. Count bounded net-decreasing macros, not every isolated move

The planner first searches for an absorbed move, prioritizing the largest
verified drop in W. If none exists, it tries one arbitrary edge subdivision,
followed by absorbed moves, up to an explicit length limit ell. A macro is
accepted only after its complete verified endpoint has strictly smaller W.
Each intermediate stellar update is exact even when its W is unchanged or
larger. The consumer independently checks all original defect lists, blocker
witnesses, intermediate weights and macro checkpoints; it does not trust the
planner's selection or a declared delta.

For s accepted macros of total t subdivisions,

    t <= ell * (W(initial)-W(residual)).                           (5)

If no higher defect remains, the refined complex is flag, has M=m+t vertices
and the same sphere dimension. The classical normal-flag theorem, followed by
#261's same-dimensional carrier maps, gives

    diameter(original P) <= m-d+t <= m-d+ell*W(initial).            (6)

If the planner stalls, it explicitly keeps the residual high support B and
uses the old residual-block refinement. Its actual vertex count is

    M=m+t-|B|+f_B,

where f_B is the number of nonempty induced residual faces. Only M-d is claimed.
Equation (5) controls the successful prefix, not that potentially expensive
completion. A trial cap is not a proof that no better macro exists. W(initial)
itself may be exponential in the original number of labels. Neither (5) nor
(6) is a universal polynomial diameter theorem.

### An actual polytope where no single step lowers W

The input fixture contains ten integer points in dimension five. Translate
them by their mean and polarize with inequalities (point_i-mean).x<=1. The test
reconstructs all 252 square active systems in exact rational arithmetic, obtains
36 simple vertices, and verifies every original row is a genuine facet. The
floating hull used only to FIND this example is not used by the final proof
consumer or exact reconstruction.

The greedy absorbed sequence has W: 9 -> 7 -> 5 -> 3. At the last state its
only higher defects are 234, 278 and 457. The entire minimal-nonface list is
saved in the report. Every edge contained in one of those triples gives W>=3;
the test evaluates all nine possibilities using (1). An edge contained in no
higher nonface cannot remove any old higher nonface, so it cannot lower W either.
This is a plateau of the ACTUAL potential, not merely failure of a chosen tie.

Subdividing 34 leaves W=3, then two absorbed moves yield 3 -> 2 -> 0. Thus a
three-step macro crosses the plateau. The complete six-subdivision refinement
has M=16, compared with M=266 for #261's twin-only/residual-block construction;
its all-pairs bound is eleven original edges. This is not a proof that every
plateau can be crossed in three steps. One tested endpoint pair still receives
a nonshortest path, and its original route may reenter a facet.

## 3. A uniform quadratic-size schedule on cyclic four-polytope boundaries

This is a counted flag-refinement class, not a new best four-dimensional
diameter theorem. Let C(n,4), n>=6, be the cyclic polytope with moment-curve
vertices (t,t^2,t^3,t^4), in increasing t order. Label them on the cyclic order
0,...,n-1. The higher minimal nonfaces of its boundary are exactly the stable
triples of this cycle: triples containing no cycle-adjacent pair. Their number is

    q = n(n-4)(n-5)/6.

For completeness, the facet description follows directly from the sign of a
quartic through four chosen moment parameters. A supporting quartic has its
negative intervals empty of all other parameters, giving two disjoint adjacent
pairs, or has no parameters outside its first and last roots, giving the wrap
pair plus a middle adjacent pair. Hence facets are unions of two disjoint cycle
edges. A four-element set with no stable triple is either a length-four path
or two disjoint edges, and is such a facet. Any larger set contains a stable
triple (the n>=6 restriction avoids the five-cycle exception). Every pair is
a face and a stable triple is not; this proves the complete minimal-nonface
classification rather than importing an incomplete triple inventory.

During absorbed subdivisions of pairs of ORIGINAL cycle labels, the higher
family remains a subset of these original stable triples. Its survivors are
exactly those not containing an already subdivided original pair. No new label
belongs to a higher defect; the new labels participate only in missing pairs.

### Stage A: process all original cyclic distance-two chords

For E={i-1,i+1}, subdivide it only if a high triple still contains it. Consider
a mixed surviving triple {u,a,b}, u in E, v the other endpoint. At most one of
a,b can be adjacent to v: of v's two neighbors, one is adjacent to u and thus
cannot appear in this stable triple. Choose w in {a,b} nonadjacent to v. If
{v,w} was subdivided earlier, it is a missing-pair blocker. Otherwise {u,v,w}
is a surviving shared high triple: its u,w pair is allowed because the mixed
triple survives, v,w has not been cut, and E is currently a face. This shared
triple supplies (2). The symmetric mixed case is identical. Every prescribed
Stage-A move is therefore absorbed.

After this stage, no surviving triple contains a cyclic distance-two pair.
Such a pair was either removed or was already in no survivor when considered;
the survivor family only decreases.

### Stage B: process within two contiguous halves

Now EVERY remaining original pair contained in a high triple is an absorbed
choice. Indeed, in the preceding argument both a,b could be adjacent to v only
if they formed its two-neighbor, distance-two pair, which no surviving triple
contains. The same pair-or-shared-triple blocker proof therefore applies.

Partition the cycle into contiguous parts of sizes a=floor(n/2), b=ceil(n/2),
and process each within-part pair whenever it belongs to a surviving high
triple. Every triple has two labels in one part, so no higher defect survives.
Each original pair is subdivided at most once.

There are n distance-two chords. Within the two parts there are
binom(a,2)+binom(b,2)-(n-2) non-cycle pairs, of which n-4 were distance-two
chords already counted. Thus the total number of subdivisions is at most

    T_n = binom(a,2)+binom(b,2)-n+6.                             (7)

The resulting flag refinement has at most n+T_n vertices and its carrier route
bound is n-4+T_n. The schedule is valid for every n>=6, not just the tested
n=6,...,16. The concrete greedy planner can be smaller: n7/n8 uses four/six
moves and M11/M14, whereas this uniform schedule uses five/eight and M12/M16.
The report keeps these algorithms and counts distinct.

## 4. Higher-dimensional examples: repeated geometric wedges

One may replace an original facet label i by a group C_i of a_i>=1 labels using
ordinary wedge operations on the primal. Explicitly replace a_i.x<=b_i by

    a_i.x+s<=b_i,      a_i.x-s<=b_i,

and retain the other rows independent of s. The result is bounded whenever
the base is bounded, because |s| is bounded by the old slack, and has one more
dimension and one more genuine facet. It is simple: old vertices on that facet
produce one vertex with both new rows tight; other vertices produce the two
slack endpoints. Equivalently, a convex decomposition at the base vertices
lifts every wedge point using their slack endpoints, showing these exhaust
its vertices.

The exact face-intersection rule proves that a minimal nonface containing the
old label replaces it by BOTH new labels; minimal nonfaces not containing it
are unchanged. A set containing only one copy can always realize that copy's
equality by choosing the sign of s, so it introduces no new minimal nonface.
Iterating produces a simple original polytope with

    m=sum_i a_i,       d=4+m-n,       e=n-4,

whose higher nonfaces are the unions of the clone groups of each stable triple.
Each group has equal higher incidence. Compress it in a_i-1 old safe moves,
then run the new quadratic schedule on the n representative labels. Old labels
outside the current high support create only additional good vertices and do
not disturb the representative stable-triple list. This gives

    t <= m-n+T_n,
    M <= 2m-n+T_n,
    diameter(original) <= M-d <= m-4+T_n = O(m^2).                (8)

For n>=7 these examples have connected higher-minimal-nonface hypergraph, so
they are not combinatorially nontrivial Cartesian products. Distance-two
connections and one stable triple connecting the parity classes establish
connectivity; replacing each label by a group preserves it. n6 is deliberately
excluded from this nonproduct assertion because its two high triples are
separate. No Minkowski indecomposability claim is made.

This is a small flag-REFINEMENT certificate in unbounded dimension and excess,
not a newly discovered polynomial-diameter class. Ordinary wedges also have
a direct graph description: two copies of the base graph are identified on
the wedge facet, with vertical edges at the other vertices. Therefore each
wedge raises diameter by at most one, and fixed-four-dimensional base bounds
already give polynomial diameter for this family. That independent easier
fact is not hidden to inflate the significance of (8). The value here is an
explicit inexpensive refinement schedule where #261's residual completion was
large, plus exact carriers usable by the same general framework.

## 5. Actual tests, adverse outcomes and verification boundary

The abstract stage checks all 114 labelled four-vertex complexes plus 210
seeded random antichains on five through seven vertices. For every face edge,
it compares (1) with independently subdividing maximal simplices and then
reconstructing all minimal nonfaces. Totals: 3,189 stellar updates, 1,013 absorbed
updates (546 with genuinely unequal incidences), 891 mixed-blocker checks and
10,550 adjacent-carrier checks on pure inputs. There are 931 actually increasing
potential steps in the tested set. Abstract inputs are not all spheres; only
the update and carrier claims, not flag-Hirsch bounds, are tested on them.

Six independently reconstructed original-H models give 58 endpoint pairs and
123 delivered edges, versus 129 for unchanged #261 and 122 shortest. One route
is nonshortest. There are 125 refined steps, two stationary carriers, one
original-facet reentry, 2,222 LP maximizations and 10,500 internal pivots. All
502 square-system references and facet relative-interior witnesses are exact.
The selection of models is a targeted stress suite, not a statistical claim
of universal benchmark superiority.

| original example | previous refined M | new refined M | new all-pairs bound |
|---|---:|---:|---:|
| cyclic polar, 4D / 7 facets | 70 | 11 | 7 |
| cyclic polar, 4D / 8 facets | 96 | 14 | 10 |
| cyclic polar, 4D / 9 facets | 126 | 18 | 14 |
| plateau example, 5D / 10 facets | 266 | 16 | 11 |

The family stage verifies all-size schedule instances n6..16 and nine original
wedge models. Two examples: n8 with three copies per label has dimension20,
24 original facets, M48 versus previous M128, bound28, and a four-edge selected
route. n12 with two copies has dimension16,24 facets,M60 versus264,bound44,
and a twelve-edge selected route. The uniform inequality (8) may be slightly
weaker than the actual count. The base four-dimensional graph is enumerated
only to choose test endpoints and check its moment-curve combinatorics. For
one ten-dimensional/twelve-facet wedge, all final square systems additionally
reconstruct the complete final graph and nonface list. Other larger models
use the proved wedge history and exact original-edge audits, NOT a generic
complete LP classification or full final graph enumeration.

Thirteen malformed/capped control types are rejected, including omitted mixed
defects, invalid blockers, Boolean labels, false weights, altered original
intersections/edges, and a three-step bridge offered under a one-step budget.
Six full generic-route certificates replay with geometric LP, inversion,
basis/intersection production and the planner itself disabled. BFS and finite
classification/recursion replay still occur. The raw input class is not inferred
from a handful of local bases: exact references or the class construction prove
it for our examples. Python and JSON parsing are not Lean-extracted.

    python3 scripts/test_mixed_defect_absorption.py --stage abstract
    python3 scripts/test_mixed_defect_absorption.py --stage geometry
    python3 scripts/test_mixed_defect_absorption.py --stage family

A clean replay uses only the two new scripts, the integer input fixture, and
four byte-identical old dependencies. Full reports and route certificates are
bundled and regenerate. Compact committed summaries identify themselves as
derived and hash-bind the detailed files. No hosted Lean or Prove2Me gate is
requested for research-only code.

## 6. Literature discipline and remaining unrestricted problem

The short path in the completed flag sphere uses the classical theorem of
Adiprasito--Benedetti, arXiv1303.3598. Stellar theory is classical; our absorption
and potential claims are proved from the exact recurrence rather than relying
on an overly broad assertion that arbitrary edge subdivisions reduce defects.
No historical priority or new best general diameter bound is claimed.

A material literature trap was checked: arXiv1303.5885, *Bounds on the diameters
of r-stacked and k-neighborly polytopes*, still has an abstract advertising a
strong missing-face-size diameter bound, but the current arXiv record explicitly
marks it WITHDRAWN and says the main proof has a mistake. That purported bound
is NOT an input to this work. Its abstract must not be used to convert the
current special-class result into a general theorem.

Primary reference records inspected:
- https://arxiv.org/abs/1303.3598
- https://arxiv.org/abs/1302.5197 (general stellar background only)
- https://arxiv.org/abs/1303.5885 (withdrawn; NOT a valid imported bound)

The unresolved task is to prove an original-size bound for a successful schedule
on arbitrary dual boundaries, or give a different original-edge argument. The
new criterion resolves unequal-incidence cases and a finite plateau crossing,
but not every stall. No fixed macro horizon is asserted sufficient. Neither
a small initial W, a successful short bridge at every state, nor a cheap residual
block is silently assumed. The current contribution supplies exact positive
operations, explicit failures, counted class schedules and reproducible tests
for attacking that remaining quantitative obstacle.
