# Complete tangent-star certificates for original-route exclusions

## 0. Status and the distinct contribution

This is written mathematics plus executed exact research code, not a Lean
compilation, axiom audit or Prove2Me theorem. Baseline:
`dbfd755ef4b6b2eb272c0cb70f888bf78741b5ec`. Coordination was posted and read back
on #268, comment `5690683673`. Other active work, including #270's blocked
companion integration, is not changed or moved through this contribution.

#268 already gives a sound fixed-budget original-edge encoding and independent
POSITIVE certificates. Its negative answers remain backend-only. The present
addition independently proves short-route exclusions using complete local
edge-star witnesses and finite closure. It does not reinterpret an unverified
SMT UNSAT response as a proof and does not change the existing solver.

The second result is a parameter-uniform capping control on the CLASSICAL
Klee--Walkup example. Every cap sum(x)<=C with C>18 preserves all its old finite
vertices/edges but permits a shortest five-edge NONREVISITING path. Unbounded
input has no nonrevisiting path at any length. Thus preserving every old finite
edge does not preserve the forced-reentry property. This is not a new Hirsch
counterexample, not a claim about every cap, and not a historical-priority claim.

## 1. Vertex and edge ranks, including nonsimple presentations

Let P={x in R^d:A x<=b}, with finite rational data and genuine vertex endpoints.
The H description may be redundant, lower-dimensional or unbounded. Let I(x)
be ALL rows tight at a feasible x. A chosen d-row subset B and rational matrix
R satisfying A_B R=I_d prove that x is a vertex. In any convex decomposition
of x, each B row is tight at both points, so invertibility makes both points x.
Conversely, if all active rows have rank below d, a nonzero common null direction
permits sufficiently small feasible displacements in both signs, contradicting
extremality. All inactive rows have positive slack; there are only finitely many.

At the relative interior of an edge, the active rows have rank d-1. More
generally, near a relative-interior point of a face the inactive rows stay
strict, so the local dimension equals d minus the active-row rank. This includes
affine-hull equality rows in lower-dimensional descriptions. Along the interior
of the segment between two feasible points, an inequality is tight exactly
when it is tight at both endpoints. Therefore two DISTINCT vertices are
adjacent iff their common active rows span rank d-1. Row COUNT is insufficient.
These are the same geometric rank facts used by #268, not new discoveries.

A positive path carries a d-row inverse at each vertex and a d by (d-1) right
inverse for chosen common rows at each edge. The consumer only multiplies
rational matrices; it does not perform elimination or trust a rank oracle.

## 2. A complete outgoing-star certificate

For a certified vertex x define

    h = -sum_{i in I(x)} a_i,
    S_x = {r : a_i r<=0 for i in I(x), h r=1}.

Every nonzero feasible tangent direction r has h r>0: the summands -a_i r
are nonnegative, and equality of their sum would put r in the common kernel
of the full-rank active rows. Thus an outgoing edge direction can be uniquely
normalized to h r=1. The section S_x is bounded: an unbounded sequence, divided
by its norm, would limit to a nonzero tangent vector with h r=0. It can be
empty at an isolated vertex, which is allowed.

Enumerate EVERY (d-1)-subset J of I(x), in a fixed public order, and form

    M_J = [h; A_J].

For each J supply one of these directly checked alternatives:

* A nonzero vector z with M_J z=0, proving this square system singular.
* A full right inverse R_J, whose first column r solves M_J r=e_1, and an
  active row i with a_i r>0, proving this candidate outside S_x.
* A full right inverse R_J with all active a_i r<=0. Bind its first column
  to a listed outgoing normalized ray.

The consumer checks the exact number binom(|I(x)|,d-1) of entries and their
fixed-order identities. It rejects omitted subsets, unused rays, duplicate
normalized rays, zero kernel witnesses and false inverse products. No producer
neighbor list is trusted as complete.

Why this covers every FINITE edge: for a true neighbor y, r=(y-x)/(h(y-x))
has d-1 independent active equalities along that edge. Choose their labels J.
Together with h these rows are independent, so its corresponding entry must
produce exactly r; it cannot be a valid singularity or infeasibility entry.
This directly establishes coverage without assuming a precomputed graph.

For every feasible ray r, use ALL original rows, not just I(x). If a_i r<=0
for every i, the ray is unbounded and has no second finite vertex. Otherwise
its finite endpoint is

    y=x+alpha*r,   alpha=min_{a_i r>0}(b_i-a_i x)/(a_i r)>0.

The record supplies alpha, y, a positive-rate blocking row, and y's vertex
certificate. Checking every inequality at y and equality at that blocker
proves exact maximality; no ratio minimization is run by the consumer. The
common J rows put x,y in a one-dimensional face, hence this is an ordinary
edge. An unbounded ray cannot be discarded as a finite neighbor or used as
an endpoint at infinity. Duplicated bases for one ray are merged explicitly.

For d=1, J is empty and M_J=[h], exactly as required. At a nonsimple vertex the
subset enumeration can be large. Lower-dimensional examples remain valid
because their equality rows are part of the complete active set.

## 3. Finite coverage proves absence, not merely failed search

For an unrestricted length budget L, a negative certificate contains a finite
vertex set, integer depth labels, and a complete star at every vertex labelled
less than L. The source has depth zero; the target is absent. EVERY finite
neighbor of each expanded vertex must be present with depth at most one larger.
Induction along ANY path of length at most L puts its j-th vertex at a listed
depth at most j. Consequently its endpoint cannot be the target.

These labels need not be trusted BFS distances. The checked local coverage and
inequalities alone prove the induction. A maliciously smaller label only forces
more star expansion. Boundary vertices at depth L need not be expanded. Extra
vertex packets may be needed to name rejected transitions; they are not thereby
claimed reachable.

To test reentry restrictions, use state (vertex,left,used). Here left contains
original row labels previously left, and used counts subsequent entries. On
x->y, let I=I(x), J=I(y). The transition is exactly

    used' = used + |(J minus I) intersect left|,
    left' = left union (I minus J).

For bound B, only successors with used'<=B require coverage. The consumer checks
the exact update; erased history cannot make a false exclusion pass. With an
explicit B and no length bound, closure at EVERY listed state proves absence
of a B-reentry walk of ANY length. The finite memory space can be exponential;
we do not assume the bound B is sufficient for arbitrary pairs.

On an irredundant genuine-facet presentation, B=0 is exactly a nonrevisiting
facet path. For arbitrary redundant rows it is an ORIGINAL-ROW restriction,
not falsely called a facet statistic. The test records preserve that distinction.
A restricted exclusion is not an unrestricted distance lower bound. Geometric
paths exist in the forced-reentry example despite its B=0 exclusion.

## 4. Uniform certificates over an entire real parameter ray

For constant A and affine b(t), vertex coordinates and finite ray lengths may
also be affine in t. `affine_route_exclusion.py` checks ONE combinatorial/rank
and closure template at t=1, then separately checks all universal geometry:

* Every declared active slack is the zero affine function.
* Every other slack a+b*t has a,b>=0 and (a,b)!=(0,0), making it strictly
  positive for EVERY real t>0; these conditions are also necessary on that ray.
* Every finite step has positive affine length, its neighbor identity holds
  coefficient by coefficient, every original remaining slack is nonnegative,
  and its claimed blocking slack is identically zero.

The normal matrices, inverses, singularity witnesses and normalized directions
are constant because A and the complete active sets are constant. Distinct
certified vertices cannot collide while retaining different exact active sets;
vertices with the same active set would already coincide at the template.
Therefore the complete-star coverage and finite closure transport to all t>0.
The same checks prove a uniform positive path with fixed shared-row inverses.

The producer MAY propose coefficients from runs at t=1 and t=2. That is only a
proposal mechanism. Two sample runs are NOT the proof. The consumer verifies
coefficient identities and the signs on the entire ray. Negative controls add
K*(t-1) to a vertex coordinate or step length: the template is unchanged, but
the universal check rejects it. The domain t>=0 is not silently substituted;
active sets change at the excluded boundary t=0.

## 5. Parameter-uniform capping and a forced-reentry control

Use the <= version of the classical U_4 matrix printed in Borgwardt, Stephen
and Yusun, *On the Circuit Diameter Conjecture*, arXiv:1611.08039v2, Section4.1:

    [ 6, 3, 0,-1] x <= 1
    [ 3, 6,-1, 0] x <= 1
    [35,45,-6,-3] x <= 8
    [45,35,-3,-6] x <= 8
    x_i >= 0, i=1,...,4.

Let u=(0,0,0,0), v=(1,1,8,8). Source facet labels are 4,5,6,7 and target
labels 0,1,2,3, using ZERO-BASED row numbering. The input is UNBOUNDED.
The classical distance five is attributed, not rediscovered. #268 already
checked the cap at19 and the distance with a full reference graph.

New independent exclusions on U_4 use a 14-vertex truncated certificate to
exclude four edges, and a 17-state memory closure to exclude every nonrevisiting
walk at ANY length. The latter checks 14 complete stars, 56 active subsets,
16 permitted and42 forbidden-memory transitions, and10 unbounded rays. A
separate five-edge positive certificate has exactly one reentry. Hence the
minimum reentry count is one, not just an observed bad selector trajectory.

Now add sum(x_i)<=C, C>18. The resulting P_C is bounded because x_i>=0.
The point with all coordinates1/100 is strict. Nine affine relative-interior
witnesses, checked over the whole parameter ray, prove all nine ORIGINAL rows
are genuine facets. Complete enumeration of all70 old square active systems
has4 singular,51 infeasible and15 distinct finite vertices; every old finite
vertex has coordinate sum at most18. Thus EVERY old finite vertex and finite
edge survives every one of these caps strictly. Nevertheless the following
path, valid for every real C>18, is nonrevisiting:

| step | point | complete active set |
|---|---|---|
|0|(0,0,0,0)|4567|
|1|(0,0,0,C)|4568|
|2|(0,1/6,0,C-1/6)|1468|
|3|(0,C/10+1/6,3C/5,3C/10-1/6)|1248|
|4|(1,C/10-4/5,3C/5-14/5,3C/10+13/5)|0128|
|5|(1,1,8,8)|0123|

Each set is exact throughout C>18; all its four normals are independent and
consecutive sets share three independent normals. Thus every segment is a
genuine original edge. Every label appears in one contiguous run. The cap
provides new edges, even though it destroyed none of the old finite graph.

Set t=C-18. The uniform negative certificate rules out paths of at most FOUR
edges for ALL real t>0. Its layer sizes are1,4,8,9,4:26 vertices,22 expanded
stars,88 subset entries,88 finite closure transitions, and1035 affine geometry
checks. The target's active set0123 does not occur. The positive five-edge
certificate has54 affine checks. Therefore

    dist_{P_C}(u,v)=5 and min facet reentries=0, for EVERY real C>18.

This is a continuum result from exact identities, not a claim based on many
large cap samples. It demonstrates why a distant cap does not inherit the
unbounded model's forced-reentry property. It does NOT assert that every cap
or every unbounded obstruction behaves this way. For P_C, m-d=9-4=5, so it
is not a bounded Hirsch counterexample and says nothing adverse about a
polynomial bound. The paper also discusses edges created by caps at infinity;
we do not claim priority for the general capping warning.

As an elementary consequence, the k-fold Cartesian product of U_4 has endpoint
distance5k and minimum total facet reentries k; the product of k capped factors
has distance5k and minimum reentries zero. Product edges change exactly one
factor; project any walk to each factor and count, then concatenate optimal
factor routes for equality. This is a WRITTEN consequence, not a separately
executed product-graph experiment, and still not a bounded counterexample.

## 6. Completed tests and precise limitations

The primary suite saves43 positive and42 negative certificates, all85 replayed
with solve, inversion, elimination, vertex production and star discovery disabled.
Eight reference models cover cubes, a nonsimple pyramid, the octahedron,
a lower-dimensional embedded square, duplicate and zero rows, and Birkhoff3/4.
Thirty-two selected reference pairs are tested at the exact shortest length
and one shorter. Independent SymPy graph construction checks13 expanded stars.
Birkhoff reference vertices come from the classical permutation description;
completeness is not inferred from sampling doubly stochastic matrices.

The Birkhoff4 diagonal trap receives an independent one-step exclusion using
ONE complete nonsimple star:495 active subsets,20 neighbors,21 coverage states.
Its eight common rows have rank seven, not eight. This reuses #268's genuine
facet control rather than claiming the example itself new. The certificate
now establishes the negative result without trusting the SMT backend or graph.

Klee--Walkup runs separately test unbounded input and caps18.001,19,100,10^6,
with length4/5 and unlimited zero-reentry questions. The uniform certificate
covers all C>18 independently of these samples. Independent reference graphs
for U_4 and P_19 have15/27 vertices and24/54 edges, from70/126 complete bases.
Three dense affine-coordinate/positive-row-rescaling runs retain the outcomes.
Embedded segment and isolated-point controls are also included.

Seventeen finite-certificate forgeries and six uniform-certificate forgeries
are rejected. Three resource limits return UNKNOWN without a false negative
certificate. Source tests are not claimed to exhaust all malformed inputs.
The producer may explore exponentially many vertex states or active subsets.
The consumer has no SMT, graph search or elimination, but still checks a
potentially exponential explicit certificate. No polynomial original-H runtime,
universal short path, arbitrary-bit-cost estimate or nonrevisiting existence
conjecture is asserted. This contribution is not a proof of Polynomial Hirsch.

All four scripts reran in a clean four-source workspace. Both full reports and
all four serialized certificate/input fixtures reproduce byte-for-byte; there
are no timing fields excluded from this comparison. The reports bind source
hashes. Test references use installed SymPy only; both consumers need only the
Python standard library. Nothing is Lean-extracted or kernel-verified.

## 7. Reproduce and next mathematical use

    python3 scripts/test_original_route_exclusion.py --out /tmp/tests.json --fixtures /tmp/exclusions
    python3 scripts/test_affine_route_exclusion.py --out /tmp/affine.json --fixtures /tmp/exclusions/affine
    python3 scripts/affine_route_exclusion.py /tmp/exclusions/affine/family.json /tmp/exclusions/affine/exclude_four.json --output /tmp/uniform-negative.json

For the basic CLI, pass A,b,start,target and either --budget L or --reentries B.
Unlimited length with B=0 tests the nonrevisiting restriction, not disconnection.
For --verify, supply only the nested certificate from a saved result.

The new tool makes finite path-local exclusions independently reproducible and
allows exact parameter families, without a complete refinement or an untrusted
UNSAT answer. The next conjecture-facing use is to establish or falsify specific
BOUNDED path-local hypotheses with justified parameter coverage. A universal
sufficient polynomial length still requires new geometry. Do not re-open #267's
ruled-out universally small complete forward stellar strategy, or disguise a
small certificate/short route assumption as a solution.

Primary attribution: https://arxiv.org/abs/1611.08039 (matrix in v2 Section4.1).
Repository interfaces: research/ORIGINAL_ROUTE_BMC.md and its existing exact
rank certificate logic at the frozen baseline. No historical novelty claim is
made for tangent-cone enumeration, graph closure, automaton memory, or the
classical Klee--Walkup distance.
