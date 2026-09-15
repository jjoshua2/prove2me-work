# Shielded mixed subdivisions and an exact defect-weight ledger

## 0. Scope and relation to the current frontier

This is an add-only research continuation of #261, developed from main
`13fd398df7dc224deccef4cd2c1506069ed042a3`. It preserves the previous twin-incidence
compressor, the flat block refinement, original edge auditors and accepted proofs.
It is a written mathematical argument with exact finite/rational tests, NOT a
Lean compilation, axiom audit or Prove2Me acceptance.

A simplicial complex is flag precisely when every minimal nonface has size two.
In a simple polytope's dual boundary, a minimal nonface records a minimal empty
intersection of original facets. We call one of size at least three a higher
defect. #261 subdivides an edge only when its endpoints have identical nonempty
higher-defect incidence. That prevents new higher defects but genuinely stalls,
including on the cyclic four-polytope examples with seven or eight vertices.

The present extension supplies:

1. An exact necessary-and-sufficient shielding test for the absence of NEW higher
   descendants, allowing unequal endpoint incidences.
2. An exact integer balance that can authorize even unshielded mixed subdivisions
   when the higher-defect weight they remove exceeds the new weight they create.
3. An explicit polynomial-size shielded flag refinement for the entire boundary
   family C(n,4), n>=6, and a rational polytopal example where every no-splitting
   move stalls but the weighted rule completes.

No theorem asserts that every polytopal complex has an available descending
move, or that its initial higher-defect weight is polynomial in original facet
count. The supplied complete finite complex is the new algorithm's input; it
is NOT a new efficient H-to-minimal-nonface classifier. The geometric tests
explicitly enumerate original face data and refined graphs.

## 1. Exact residue form of the stellar update

Let K have complete minimal-nonface antichain N, all sets of size at least two.
Let E={u,v} be an actual FACE edge, and z a fresh vertex. Define

    R_E = minimal_inclusion {N minus E : N in N, N intersects E}.

Each residue is nonempty because E is a face. The minimal nonfaces after stellar
subdivision are EXACTLY

    {E}, all old N with E not contained in N,
    and {z} union R for R in R_E.                              (1)

This refines the earlier #261 membership formula; the underlying stellar operation
is classical, not a new topological construction.

Proof: a set without z is a new face exactly when it is an old face not containing
E. A set {z} union U is a new face exactly when U does not contain E and U union E
is an old face. A minimal old obstruction in U union E either avoids E, or leaves
a residue contained in U. Taking inclusion-minimal residues gives all new
z-containing minimal nonfaces. No old nonface can lie inside a residue, because
the residue is a proper subset of another old minimal nonface. No residue contains
u or v. Thus the three displayed groups remain minimal without additional hidden
cross-cancellations. The code computes (1) and the independent reference performs
the literal stellar operation on maximal simplices and compares EVERY face.

## 2. Exact criterion for no new higher descendants

A common higher nonface N with E contained in N produces the descendant

    (N minus E) union {z}.                                   (2)

This descendant is always minimal. If a smaller residue M minus E lay inside
N minus E, then M would be a proper subset of N, contrary to old minimality.
This includes old missing pairs as possible M. Different common descendants
cannot newly contain each other.

A one-sided higher nonface N meets E in exactly one endpoint. Its potential
descendant has the SAME size as N and can create additional higher defects while
the old N remains. It is suppressed if an existing smaller residue blocks it.
All such new higher descendants are absent if and only if, for EVERY one-sided
higher N, there exists an old minimal nonface M satisfying

    M intersects E;
    either |M|=2 or E is contained in M;
    M minus E is contained in N minus E.                     (3)

We call (3) shielding. It does not require equal incidence signatures.

Sufficiency: an old missing pair gives a singleton residue and hence a new missing
pair, while a common higher M gives the inherited descendant (2). Either blocks
the one-sided potential descendant. Necessity: if a one-sided residue has no
such blocker, descend to an inclusion-minimal residue inside it. A minimal
residue exists since the list is finite. It cannot come from a missing pair or
common higher nonface by assumption. It therefore comes from a one-sided higher
nonface, has at least two labels, and creates a genuinely new higher descendant.
This proves both directions, not merely a sufficient heuristic.

The old twin condition is the vacuous case: there are no one-sided higher
nonfaces. Shielding can instead use smaller common defects or missing pairs.
All original vertices u,v remain vertices of the refinement; this is not a
quotient identifying original facets.

## 3. Count births as well as eliminated weight

Define the nonnegative integer

    W(K) = sum_(N higher) (|N|-2).

Let c_E be the number of old higher nonfaces containing E. Let B_E be the NEW
higher z-descendants other than the common descendants (2), after all residue
minimization, and put

    D_E = sum_(B in B_E) (|B|-2).

The exact balance is

    W(K_E) = W(K) - c_E + D_E.                               (4)

Every common higher nonface shrinks by one; even a triple becoming a missing pair
reduces W by one. Old higher nonfaces not containing E persist. Newborns account
for every other higher contribution. That proves (4) without assuming monotonicity
of the number of defects or their sizes.

The broader admissibility condition is D_E<c_E. It includes productive shielded
moves (D_E=0), but permits controlled splitting. For a sequence of t such moves,

    W_t = W_0 - sum c_E + sum D_E,
    t <= W_0-W_t.                                           (5)

The method returns flag, a verified local stall, or an explicitly capped partial
sequence. Equation (5) bounds completed moves even if it stalls; it does NOT
prove that a next descending edge always exists. Every descending edge is in
at least one higher nonface, so checking pairs contained in higher nonfaces
covers all possible strict W-decreases.

For a dual (d-1)-sphere, every minimal nonface has size at most d+1. Hence if q
is its initial higher-defect count, W_0<=(d-1)q. CONDITIONAL ON reaching flag,
this yields a refined size M=m+t and original diameter bound

    diam(P) <= M-d = m-d+t <= m-d+W_0.                       (6)

Neither q nor W_0 is polynomially bounded for arbitrary inputs by this argument.
Do not replace the completion condition by the fact that our tested examples
complete. This is not an unconditional new few-defect theorem replacing #261's
always-available residual-block fallback.

An edge contained in a higher defect need not decrease W. On C(7,4), subdividing
E={0,3} consumes one common higher triple but creates two unshielded triples:
W goes from seven to eight. Its input and literal stellar reference are stored
as a negative control. The present proof uses the full residue balance instead
of relying on an unqualified decrease claim for a selected edge.

## 4. Transport still gives genuine original edges

The carrier proof of #261 is valid for ANY actual edge stellar subdivision,
not only twin or shielded moves. A refined maximal d-vertex simplex containing z
contains exactly one endpoint of E. Replacing z by E recovers a d-vertex original
maximal simplex. Adjacent refined facets share d-1 vertices, and their carriers
are equal or share at least d-1 original vertices. Applying every stellar map
backward preserves this property at every level.

Compatible lifts of the endpoints choose which member of E to replace so that
their common refined face carries all original shared labels. A refined path
inside that common-face star therefore preserves every original common facet.
After deleting stationary carriers, all remaining steps are original facet
exchanges. The rational tests additionally audit the entire maximal edge against
the original H-rows, so this is not arbitrary extension projection to a chord.

Subdividing a simplicial sphere preserves its topology, purity and normality.
If the final subdivision is flag, Adiprasito--Benedetti's classical theorem gives
a refined facet path of length at most M-d. Use the link of the common lifted
face for the face-preserving version. Its bound is no larger than M-d. Thus (6)
is about ORIGINAL polytope graph distance. We do not reprove or republish the
classical flag-normal theorem here.

The test harness uses BFS on an explicitly generated refined facet graph. That
is legitimate evidence for these finite carriers, but is NOT an efficient
implementation of the classical combinatorial-segment algorithm. Enumerating
that graph can be expensive or exponential even when the new vertex count is
moderate. The production transport checker receives a finite path and does not
search for it.

## 5. An all-n shielded schedule for C(n,4)

For n>=6, Gale evenness says that facets of the boundary of C(n,4) are unions of
two disjoint edges of the n-cycle. Its minimal nonfaces are precisely the stable
triples: three labels with no cyclically adjacent pair. The equivalence also
follows directly: a subset with no stable triple has at most four vertices and
can be covered by two disjoint cycle edges. For n>=6 an induced proper subgraph
of the cycle is a union of paths; the exceptional odd whole-cycle cases contain
a stable triple. There are n(n-4)(n-5)/6 stable triples and no missing pairs.

Use ONLY pairs of original labels, and maintain the invariant that all higher
nonfaces are surviving original stable triples. Each shielded subdivision then
turns its common triples into missing pairs. All already selected original
pairs remain missing pairs forever.

Phase one processes each distance-two cyclic pair {i-1,i+1}, skipping it when
no current higher triple contains it. Such a productive pair E={u,v} is shielded.
For a one-sided triple {u,a,b}, at least one of a,b is not a neighbor of v: both
neighbors of v cannot occur because one is adjacent to u. Call that label k.
The original triple E union {k} was stable. If it survives, it is a common
blocker in (3). If not, it was removed by an earlier selected pair. That earlier
pair cannot be E, which is currently a face, or {u,k}, which is inside the
current nonface {u,a,b} and hence is a face. It must be {v,k}, and this permanent
missing pair supplies the shielding blocker. The argument with u,v exchanged
covers the other side.

After phase one, no surviving higher triple contains both cycle neighbors of
any vertex. Now choose ANY pair E={u,v} in any surviving higher triple. For a
one-sided triple {u,a,b}, at least one of a,b is not a neighbor of v; otherwise
{a,b} is a distance-two pair that phase one already eliminated from all higher
triples. The SAME common-triple-or-missing-pair proof shows that E is shielded.
Consequently phase two can continue until no higher triple remains.

Each move selects a distinct original nonadjacent pair. There are n(n-3)/2
such pairs. Thus the schedule is complete and has

    t <= n(n-3)/2,    M=n+t <= n(n-1)/2.                     (7)

This is a polynomial flag-refinement certificate for the entire CYCLIC
FOUR-DIMENSIONAL family. The dimension is fixed; stronger classical diameter
bounds are already available for low dimensions. Equation (7) is NOT a new
best diameter estimate and does not solve the unrestricted problem. It does
show that the earlier no-twins stall is not intrinsic even when q grows cubically.

The explicit deterministic schedule is different from the greedy shielded
schedule. At n7 it uses five rather than four steps; at n8 it uses eight rather
than six. The theorem favors a provable schedule, not an optimal one. It is
executed at n6,7,8,9,10,12,16,20. The n20 case has800 higher triples and uses122
moves, with M142<=190. Only finite nonfaces and their updates are enumerated in
these larger family checks, not original/refined route graphs. Initial stable
triple catalogues are independently compared with complete Gale facet closures
through n12; the all-n identification is the written argument above.

## 6. Shielding itself can stall on a rational polytopal sphere

Start with ten moment-curve vertices in dimension six, translated by their mean
so that zero is strictly interior. Stellarly subdivide, in order, the edges

    {3,6}, {2,7}, {0,3}, {5,8}.

Their new labels are10,11,12,13. To realize each operation rationally, take the
edge midpoint p and add (1+epsilon)p for sufficiently small rational epsilon>0.
Facet inequalities are normalized to a_F.x<=1. The code chooses epsilon below
half every positive slack-to-slope threshold for a nonincident facet. Exactly
the edge-star facets are visible, giving the literal stellar boundary. Every
new supporting facet is then checked against every vertex with exact rational
strictness. No merely abstract sphere is claimed polytopal without realization.

The polar of the final simplicial polytope is a simple six-dimensional ORIGINAL
H-polytope with14 genuine facets,136 vertices and408 graph edges. Its higher
nonfaces consist of17 triples and40 quadruples, so W=97. It has no productive
shielded edge at all (nor twin edge); the complete productive pair scan verifies
that local stall.

The weighted policy nevertheless reaches flag in29 further stellar moves.
Ten of those moves create new higher descendants. The first, E={4,6}, consumes
11 old higher defects, creates two triples, and changes W from97 to88. Across
the complete schedule, sum c_E=114 and sum D_E=17, giving97-114+17=0 exactly.
The final refinement has43 vertices and834 maximal simplices. Its original
all-pairs diameter certificate is M-d=37. This is a sufficient bound, not the
measured shortest distance or a record diameter estimate.

All original facets are certified genuine by a feasible point tight on exactly
that row. Sampled transported paths preserve common original facets and pass
the original inverse-column/maximal-step auditor. The example therefore shows
that ALLOWING BIRTHS can be necessary to leave a no-splitting local stall while
still keeping a strictly decreasing, fully accounted resource.

There is no corresponding universal claim. The six-label nonpure complex with
minimal nonfaces014,035,125,234,0245,1345 is a genuine local stall even for the
weighted rule: every productive edge has weight change at least zero. It is
NOT a polytopal sphere and is explicitly labeled nonpure. It refutes a proposed
universal descent assertion for arbitrary complexes only; the existence of
budget-descending moves for all polytopal states remains unproved here.

## 7. Executed checks and their boundaries

    python3 scripts/test_stellar_defect_budget.py

Four stages: algebra, geometry, family, negative, then assemble. Exact source
and dependency hashes must agree across the staged receipts.

Algebra: all1,024 subsets of the ten possible triples on five labels, plus96
mixed-size random antichains, yield1,120 complexes. All11,501 face-edge stellar
updates are checked against literal subdivision of maximal faces, including
880,128 independent face-membership comparisons. There are6,257 shielded updates
with unequal incidences and39 unshielded weight-decreasing updates. The1,652
weight-increasing updates are retained rather than ignored. The shielding iff,
newborn list and exact integer balance pass in every case.

Geometry: seven rational simple polars are independently built. Initial cyclic
facets from Gale evenness are cross-checked by exhaustive rational supporting-
plane enumeration, not used as an unverified facet list. The four preliminary
stellar cuts of the stall example have exact visibility certificates. Complete
original minimal nonfaces are classified from these face lattices. All original
and refined graphs used for route tests are explicitly enumerated.

The seven models supply397 endpoint pairs,881 refined steps,866 transported
original edges and15 stationary carrier steps. Independent original shortest
paths total843 edges;22 delivered routes are nonshortest. No universal optimality
or default benchmark superiority is claimed. Every retained original edge is
checked for original feasibility, exact simple active inverse, common facet
exchange and maximal step. Common facets are preserved. The stored sample
certificates replay with inverse discovery disabled.

Family: the separate eight-instance all-n schedule tests check the stated
quadratic vertex budget without enumerating refined graphs. Seventeen forged,
malformed or non-descending/capped requests are rejected; capped outputs remain
partial, not flag-complete. Full examples and raw reports regenerate and are
bundled. The compact committed report is explicitly derived, not a platform
receipt. Python, rational Gaussian elimination in the old auditor, JSON
parsing and the classical imported results have not been formalized here.

## 8. Conjecture-facing conclusion

The general bottleneck is now sharper: unequal defect incidence alone need not
cause growth, and even actual growth can be charged exactly. The next positive
step would be a universally available sequence with controlled total net cost,
or a structural theorem bounding the input defect weight or a cheaper progress
measure for arbitrary dual polytopal spheres. Small residual cores, few defects,
and successful benchmark schedules must not be silently assumed.

This removes a restrictive safe-operation hypothesis and provides new complete
schedules, but not a uniform polynomial bound in original facet count and
dimension. No accepted/pending packet, active agent proof, Actions workflow,
secret, or dependency pin is modified or resubmitted.

## Primary sources and attribution

Karim Adiprasito and Bruno Benedetti, The Hirsch conjecture holds for normal
flag complexes, Mathematics of Operations Research40(2015), no.4,954--962,
arXiv:1303.3598v3, Theorem1.4; DOI10.1287/moor.2014.0661.
https://arxiv.org/html/1303.3598v3
This supplies the normal-flag M-d diameter theorem, not the new residue ledger.

Margaret Bayer and Tibor Bisztriczky, On Gale and braxial polytopes,
arXiv:math/0610940; DOI10.1007/s00013-007-2163-x.
https://arxiv.org/abs/math/0610940
Used for classical cyclic/Gale context; the specific cycle schedule and the
exact rational supporting-plane cross-checks are stated here.

The membership form of the stellar update and compatible carrier lifts reuse
the preceding repository research/DEFECT_INCIDENCE_COMPRESSION.md (#261).
No historical priority is claimed for all equivalent missing-face criteria.
