# Mixed stellar refinement: exact branching energy and a polytopal plateau obstruction

## 0. Contribution, provenance, and verification boundary

This is written mathematical research and exact rational/combinatorial software.
It is NOT a Lean compilation, an axiom audit, a Prove2Me theorem, or a solution
of Polynomial Hirsch. The original polytope in the geometric statements is
simple, bounded and full-dimensional, with all its genuine facets counted.

Baseline: `13fd398df7dc224deccef4cd2c1506069ed042a3`, after merged #260/#261.
The existing stellar minimal-nonface formula and backward carrier transport
are reused from #261, not claimed as new. #260 supplies the earlier flat-block
comparison. This contribution relaxes identical higher incidence to an EXACT
absorption criterion, counts actual branching with an energy identity, and
exhibits a genuine polytopal obstruction to insisting on one-step descent.
The last result includes a constructive plateau escape in every dimension >=6.

The imported classical route theorem is Adiprasito--Benedetti, *The Hirsch
Conjecture Holds for Normal Flag Complexes*, Mathematics of Operations Research
39(4) (2014), 1340--1348, DOI 10.1287/moor.2014.0661, arXiv:1303.3598. A normal
flag (d-1)-complex with M vertices has a facet path of at most M-d steps.
No historical novelty is asserted for every equivalent formulation of the
finite nonface identities or for the classical subdivision/carrier machinery.

## 1. Minimal nonfaces and the exact persistent generators

Let K be a finite simplicial complex on m vertices, specified by its COMPLETE
antichain N(K) of minimal nonfaces, all of size at least two. Let H(K) consist
of its minimal nonfaces of size at least three. In the dual boundary of a
simple polytope, a minimal nonface is a minimally empty intersection of original
facets. A complex is flag exactly when H(K) is empty.

Subdivide an actual face edge E={u,v}, adding a new label z. As established in
#261, the new minimal nonfaces are the inclusion-minimal members of

    {E},  {N in N(K) : E is not a subset of N},
    and {{z} union (N minus E) : N in N(K), N intersects E}.       (1)

The following generators in (1) PERSIST as minimal nonfaces:

* E itself;
* every old N not containing both endpoints of E;
* {z} union (N minus E) for every old N containing E;
* {z,w} from every old missing pair touching E.

Duplicate pairs are counted once. Denote this persistent family by P_E.
The only possible additional higher generators come from old HIGHER nonfaces
that meet E in exactly one endpoint; call those nonfaces mixed.

Here is the minimality proof, which matters for the exact count. Old generators
in P_E avoid z, and cannot contain E. A new generator without z could contain
an old minimal nonface only if that old nonface was already contained in it.
A smaller z-generator inside the descendant of a nonface containing E would
mean its old ancestor was contained in that old nonface, contradicting the
original antichain. Two distinct descendants from nonfaces containing E cannot
contain each other for the same reason. Missing-pair descendants are already
pairs and cannot contain a proper nonface. Finally, a mixed descendant cannot
absorb any persistent higher descendant: undoing the removal of E again gives
strict containment of old minimal nonfaces. Thus every member of P_E really
survives after minimization, not merely as a redundant generating constraint.

## 2. Necessary and sufficient no-branching criterion

For a mixed higher nonface N, write D_N={z} union (N minus E). All mixed
descendants are absorbed, so there are NO additional higher minimal nonfaces,
if and only if for every such N there is an old minimal nonface M satisfying

    [E subset M OR (|M|=2 and M intersects E)]
    AND  (M minus E) subset (N minus E).                         (2)

Sufficiency: the descendant of M is a persistent generator contained in D_N.
It is strictly smaller: equality would make an old M a proper subset of N,
or vice versa, unless it was the same old mixed nonface, which is excluded by
the condition on M. Therefore D_N is not a new minimal nonface.

Necessity: if a mixed descendant has no such persistent absorber, minimize
inside the finite collection of unabsorbed mixed descendants below it. An
inclusion-minimal one is an extra higher minimal nonface. It cannot be absorbed
by E (it contains neither old endpoint), nor by an old nonface without z (that
would already be a proper nonface inside N). Any persistent absorber with z
has exactly the ancestor forms in (2). A chain of mixed absorbers must therefore
terminate at either a persistent absorber or a surviving extra higher defect.
This proves both directions of (2).

Identical nonempty higher incidence implies (2) vacuously, since there are no
mixed higher nonfaces. The converse fails: either an OLD MISSING PAIR or a
HIGHER nonface containing BOTH selected endpoints can absorb a mixed descendant.
A criterion looking only for old pair absorbers is also unnecessarily strict.
The exact regression includes higher-dimensional cyclic examples requiring
higher absorbers, not just the pair-shield special case.

## 3. The exact energy ledger allows controlled branching

Define the integer flagness energy

    Phi(K) = sum_{N in H(K)} (|N|-2).

For a face edge E let c_E be the number of old higher nonfaces containing E.
Let A_E be the ACTUAL extra higher minimal nonfaces after minimizing (1),
namely the new minimal nonfaces not in P_E. Define

    B_E = sum_{D in A_E} (|D|-2).

Then the exact identity is

    Phi(K_E) = Phi(K) - c_E + B_E.                              (3)

Every higher nonface containing E loses exactly one unit of energy. A triangle
becomes a missing pair and contributes zero. Other old higher nonfaces persist
unchanged. The only other energy is from the additional minimal descendants
A_E. This proves (3), including overlapping absorbers and duplicate generating
sets. Counting raw generated descendants instead of ACTUAL minimal ones would
not give this identity.

In the no-branching case B_E=0. If c_E>0 this gives strict descent even when the
endpoint incidences differ. The higher-defect count decreases precisely by the
number of old containing triangles. Unlike the twin-only rule, the union of
higher-defect labels need not shrink; do not import #261's support bound t<=k-h.

More importantly, branching is affordable whenever B_E<c_E. Even the NUMBER
of higher defects can increase while Phi decreases. Section 5 gives an exact
simple polytopal example with q:12->13 but Phi:19->16, c_E=4 and B_E=1.
Thus neither identical incidence nor nonincreasing defect count is a necessary
condition for useful progress.

For an arbitrary schedule, the ledger telescopes:

    Phi_t = Phi_0 - sum_j c_{E_j} + sum_j B_{E_j}.              (4)

Any schedule of strict single-step descents has at most Phi_0 steps before it
finishes OR STALLS. Grouping at most two subdivisions into each macro, with a
strict integer energy decrease at every macro endpoint, gives at most 2*Phi_0
steps if it finishes. The intermediate energy may stay constant or rise. These
bounds do not prove the existence of a completing schedule or make Phi_0
polynomial in original dimension/facet count. There may be exponentially many
higher minimal nonfaces.

The implemented heuristic first searches productive edges (edges contained in
some higher nonface) for single-step descent. If none succeeds, it searches
pairs of productive steps for a net descent. It has explicit caps and reports
`stalled` rather than asserting universal completion. It does not search every
possible pair with an unproductive first edge. No claim that this two-step
heuristic always reaches a flag sphere is made.

## 4. From a completed refinement to ORIGINAL ordinary edges

If t stellar face-edge subdivisions of an original simplicial (d-1)-sphere
reach a flag complex, the final vertex count is M=m+t. It remains a normal
sphere. The classical normal-flag theorem and #261's carrier argument give

    diameter(original simple d-polytope) <= m-d+t.             (5)

The original facet count is m, not m+t. The latter is a refined certificate
size used to bound an ORIGINAL walk. At a single subdivision, a maximal simplex
containing z contains one endpoint of E; replacing z with both endpoints gives
its full old carrier. Adjacent maximal refined simplices have old carriers
that are equal or share d-1 labels. Composing these maps and deleting stationary
steps never creates a chord or increases path length. This is not projection
of an arbitrary extension edge.

Compatible endpoint lifts preserve all common original facets. If E occurs
at only one endpoint, drop an E-label absent from the other endpoint. If both
contain E, drop the same label on both. Their shared refined face carries the
old common labels. A normal-flag path within its link has length at most M-d,
and its old carriers preserve the original common face.

For the finite tests, the reference router explicitly enumerates the refined
facet graph and runs BFS. This is NOT an efficient arbitrary-H algorithm and
not the generic combinatorial-segment producer from #258. The independent
saved-route audit uses no BFS: it replays each carrier map, checks each refined
adjacency, and then checks every delivered original edge directly against
original H rows, an independent active basis, and maximal feasible step ratio.
Completeness of the geometric table is established separately, as below.

### Cyclic examples previously stalled under the twin rule

The six exact centered moment-curve polars all have no initial twin move.
Condition (2) nevertheless gives completed no-branching schedules:

| d | genuine m | original vertices | initial Phi | new steps t | bound m-d+t |
|---:|---:|---:|---:|---:|---:|
|4|7|14|7|4|7|
|4|8|20|16|6|10|
|4|9|27|30|9|14|
|6|9|30|18|8|11|
|6|10|50|50|13|17|
|8|11|55|33|12|15|

For the first two, #261's full residual-block fallback gave refined M=70/96
and bounds66/92. The new schedules give M=11/14 and bounds7/10. This compares
refinement certificates, not new best-known diameter estimates. Their actual
graphs are small and stronger classical estimates may apply.

## 5. Exact simple polytopal obstruction to EVERY single-step descent

A nonflag sphere need not have ANY energy-decreasing stellar face edge. The
following finite rational construction proves this within actual polytopes,
not only for an abstract nonpolytopal antichain.

Start with these ten integer points in R^6:

    (-8,-6,-4,-9, 7,246), ( 2,-6,-5,-9, 8,210),
    ( 2,-3,-5, 7,-6,123), (-9, 0, 6,-1,-3,127),
    ( 3,-1,-1, 9, 8,156), ( 7,-8, 1,-1, 9,196),
    (-2,-9, 6,-2,-7,174), (-4, 4, 0, 7,-2, 85),
    ( 0, 4,-8,-7,-4,145), ( 7, 6,-4, 4, 8,181).

Their sixth coordinates are the squared norms of the first five. Distinct
paraboloid points are exposed vertices: the corresponding tangent functional
is strictly smaller on every other point. Let a_i=10*v_i-sum_j v_j and put
P={x:a_i.x<=1}. Exact all-active-base enumeration (210 bases) verifies full
rank, 45 vertices, simplicity, and ten genuine facets. Positive normal balance
sum_i a_i=0 and full rank prove boundedness; zero is strictly feasible.
The code does not use a floating hull to establish these conclusions.

The seed has twelve higher defects, Phi=19, and no productive nonbranching
move. Subdivision E={2,3} adds label10 and gives thirteen higher defects but
Phi=16. Its one extra higher descendant is {4,8,10}; four containing old
higher defects pay for it. Another mixed ancestor {1,2,7,9} is absorbed by the
descendant of {1,2,3,9}. This is a geometric instance where branching helps.

Apply the following eight shallow ridge truncations, equivalently dual edge
subdivisions, with consecutive fresh labels10,...,17:

    (2,3), (4,8), (5,8), (1,10), (0,11), (5,10), (7,9), (6,16).

For original inequalities a_u.x<=b_u and a_v.x<=b_v, the cut is

    (a_u+a_v).x <= b_u+b_v-epsilon,

where epsilon is half the smallest POSITIVE old vertex slack in the summed
inequality. Every ridge vertex is cut off and every other old vertex remains
strictly on the retained side. New vertices are exactly the intersections
with crossing OLD edges. This elementary clipping fact proves completeness
inductively; the code independently matches those active sets to literal
stellar subdivision of maximal simplices. Every new H-table is fully audited,
including genuine-facet relative-interior points and nonsingular active bases.

The resulting P_6 has dimension6, eighteen genuine original facets, and164
vertices. Its only four higher minimal nonfaces are

    {0,5,16}, {0,6,7}, {1,2,16}, {1,4,6}.                       (6)

The complete missing-pair list is:

    0-11 0-12 0-17 1-10 1-15 1-17 2-3 3-11 3-14
    4-8 4-12 4-13 5-8 5-10 5-14 6-11 6-14 6-16 7-9
    8-15 9-13 9-15 10-11 10-12 10-14 11-13 11-15 11-17
    12-13 12-14 12-15 13-14 13-16 13-17 14-15 14-17 15-16 15-17.

All minimal nonfaces are independently recomputed from the complete original-H
vertex table, not inferred solely from the stellar update formula.

There are 115 possible dual FACE-EDGE subdivisions; these are not the original
polytope's ordinary edges. Twelve contain a higher defect. For EACH of those
twelve, c_E=1 and B_E=1, so Delta Phi=0. They are

    0-5 0-6 0-7 0-16 1-2 1-4 1-6 1-16 2-16 4-6 5-16 6-7.

Every other face edge has c_E=0 and hence Delta Phi=B_E>=0 by (3). Thus Phi=4
is a genuine local minimum under ALL single stellar edge subdivisions, though
the sphere is nonflag. The full 115-row ledger is in the serialized fixture.
This disproves the proposed universal strict-energy-descent rule. It does not
disprove Polynomial Hirsch, or even predict large diameter: the independently
reconstructed original graph has diameter8.

### A short plateau escape, not an assumed repair

The explicit word

    (0,6), (0,5), (1,4), (2,16)

with new labels18,...,21 gives energies

    4 -> 4 -> 3 -> 2 -> 0.                                    (7)

The first two steps form a net descending macro. The third step branches but
has c_E=2,B_E=1; the final step has c_E=2,B_E=0. The final complex is flag on22
vertices and has260 maximal simplices. Equation (5) gives an ALL-PAIRS original
bound16. This is weaker than the enumerated diameter8; the point is a certified
escape from a false universal local rule. The generic two-step heuristic also
escapes, but finds FIVE subdivisions and a weaker bound17. We do not confuse
the four-step explicit word with the heuristic's output or claim optimality.
The twin-only residual block has eight labels and135 nonempty induced faces,
so its bound here would be18-6-8+135=139, versus16 from the explicit repair.
This is a comparison of certificate bounds, not a comparison of actual path lengths.

## 6. A nonproduct obstruction and repair in every dimension d>=6

The example extends without a Cartesian-product excuse. Suppose P_r has dual
K_r, dimension6+r and18+3r genuine facets. Take P_r times an interval, adding
dual vertices a,b with missing pair {a,b}. Then shallowly truncate the ridge
corresponding to the face edge {3,a}, adding a new dual vertex z.

Label3 belongs to none of (6). Neither a nor3 lies in any higher nonface, so
this last stellar operation leaves all four higher nonfaces unchanged. It
creates only missing pairs involving new vertices or label3. In particular,
the induced missing-pair relation on the eight labels in (6) is unchanged.
Product and shallow truncation preserve simplicity, boundedness, and all old
facets, and add respectively two and one genuine facets. This proves by
induction that actual simple polytopes exist with

    d=6+r, m=18+3r=3d, four higher defects, Phi=4.              (8)

All twelve productive edges retain the same energy balance c_E=B_E=1. Every
other edge has c_E=0. Hence NO P_r has a single energy-decreasing stellar step.
The same four-step word (7), with the appropriate fresh labels, still reaches
flagness. During that word all higher defects use only the original eight
labels and repair labels. Additional family missing pairs always involve a
family-external label, so cannot newly absorb or create a higher descendant
entirely within that support. The four energies remain (7). Thus

    M=3d+4,     diameter(P_r) <= M-d=2d+4.                     (9)

This family is NOT a nontrivial combinatorial Cartesian product. In a join,
every minimal nonface belongs entirely to one factor; therefore the graph
joining vertices that occur together in a minimal nonface is disconnected.
The seed P_6's dual has a connected such graph. The new pair {3,a} connects the
new interval factor to the old graph, {a,b} connects b, and the descendant
{z,b} connects z. Connectivity persists. This excludes a combinatorial join
and hence a combinatorial Cartesian product of the primal polytope. No
Minkowski or projective indecomposability is asserted.

The program checks the exact abstract recurrence for every r=0,...,64. Full
rational H-tables are constructed separately for r=0,1,2: their vertex counts
are164,394,920. Large-r H-graphs are NOT enumerated; (8)--(9) there follow from
the induction, with finite recurrence checks as supporting evidence. At d32,
m96, M100 gives bound68. This is an ALL-PAIRS bound from the construction, not
a sampled endpoint distance or a new best general diameter estimate.

## 7. Execution, adverse results, and remaining unrestricted problem

The full regression contains218 abstract complexes and1910 independently
checked literal stellar operations. There are285 productive non-twin moves
satisfying the no-branch criterion. Nineteen moves decrease energy while
branching; thirteen even increase higher-defect count. The exact seed/barrier
has polytopality evidence separate from these arbitrary abstract examples.

Six complete original-H cyclic graphs supply72 endpoint pairs and159 delivered
original edges. The barrier graph supplies40 more pairs and159 original edges.
All318 original edges pass direct original-row checks. Independent original
BFS totals are156 and159 respectively, versus159 and159 delivered. Three cyclic routes
are longer than original BFS; none of the40 sampled barrier routes is longer.
These are finite reference-router measurements, not a benchmark claim against
the old project selector. All refined graphs in these tests are explicitly
enumerated. Full source minimal-nonface classification can also be exponential.

Fourteen invalid complex/step/schedule controls and five forged carrier-route
controls are rejected. The serialized verifier reconstructs the seed and all
cuts exactly, recomputes the complete barrier nonfaces and115-row energy table,
and checks40 stored routes without running routing BFS. Its stored graph-
diameter field is historical test output; that verifier does not recompute it.

The unrestricted task now has two genuine obstacles rather than a hidden
assumption. A good refinement may need branching and may need an initially
nondecreasing step. The exact ledger identifies what a successful amortized
argument must pay. We have NOT proved uniformly bounded escape macros for all
polytopal local minima, nor bounded total branching/certificate size by a
polynomial in original m,d. Phi itself can be exponential. The family (8) and
successful cyclic schedules do not establish either missing universal fact.

Reproduce from the repository root:

    python3 scripts/test_stellar_defect_energy.py --stage all --out /tmp/energy.json --fixtures /tmp/energy-fixtures
    python3 scripts/test_stellar_defect_energy.py --verify-fixture /tmp/energy-fixtures/stellar-energy-barrier.json

No third-party Python dependencies, Lean, API credentials, or hosted workflow
are needed for these research checks. The exact code, complete test output,
fixture and source-hash/clean-replay records accompany the continuation bundle.
