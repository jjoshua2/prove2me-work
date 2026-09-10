# Rank-controlled box-section repair cost

Date: 2026-09-09, America/New_York.

## Status

This is an ordinary mathematical proof and executed exact-computation result,
NOT a Lean-verified theorem and NOT a Prove2Me submission. No literature-priority
claim is made. The complete research packet `prove2me_rank_box_cost_continuation.zip`
in the conversation includes the detailed proof, self-contained exact constructor,
regressions, and reproduction script. This repository note preserves the theorem
and its proof independently of that download.

The separate five-module simultaneous-clipping Lean chain in this branch remains
UNVERIFIED. Actions run 34419838031, job 102692640995, failed before build steps
or compiler logs appeared; a log read returned 404 BlobNotFound. The cause was
not established. The branch name expresses the verification goal, not a success.
The workflow is now manual-only to avoid repeating pre-build failures. No
Prove2Me API/secret is used.

## Main theorem

Let P={x in R^m : Ax=b, 0<=x<=1}, r=rank(A). For a target vertex v let
T(v)={i:0<v_i<1}, t=|T(v)|, and let s(u,v) count the coordinates where v is at
a bound but u does not yet equal that bound. Then an ordinary edge walk satisfies

    dist_P(u,v) <= s(u,v) binom(2(r+t),r+t),
    diam(P) <= m binom(4r,2r) <= m 16^r.

Empty sections are vacuous. Degenerate and lower-dimensional sections and
dependent/zero equations are allowed. For arbitrary finite boxes, eliminate
zero-width coordinates and normalize the remaining intervals affinely. No
coefficient magnitude, integrality, or circuit-imbalance assumption is needed.
There is no claim of optimal constants or strongly polynomial running time.

## 1. Elementary low-excess common-face bound

For a pointed q-dimensional polyhedron Q described by f inequalities, set e=f-q.
Redundancy is allowed. Any two vertices x,p have a minimal common face F of
dimension h<=min(q,e): choose q independent tight rows at each endpoint; their
index sets share at least 2q-f=q-e independent rows. There are at least q-h
independent rows identically tight on F. Use these as affine-hull equations,
leaving at most f-(q-h)=e+h inequalities. Every vertex of F has h independent
tight rows, so

    |vertices(F)| <= binom(e+h,h) <= binom(2e,e).

One can construct an edge route inside F by strictly decreasing the sum of
slacks of the rows tight at p. This nonnegative objective has p as its unique
zero. At any other vertex, the direction toward p decreases it; the tangent
cone has an improving extreme direction. That direction cannot be an unbounded
edge ray, since the objective is bounded below. Therefore some bounded incident
edge decreases it. Strict descent never repeats a vertex and reaches p within
binom(2e,e)-1 steps. This counts actual bounded edges even when Q is unbounded;
it is not an application of a bounded-polytope Hirsch theorem.

## 2. First-hit access needs at most one extra edge

Let a compact R be obtained from pointed Q by finitely many new cuts. Suppose
an old vertex x is strict in all the new cuts, and a new cut plane meets R.
If the old vertex graph has diameter <=D, there is an R-edge route from x to
one of the new cut planes with at most D+1 steps.

For bounded Q, maximize a cut functional and join x to an old maximizing vertex
on/beyond the plane, stopping at the first new equality. This uses at most D
steps. For unbounded Q, cap it beyond all old vertices and all of R. In affine
coordinates Q={z:N_j z<=c_j}, pointedness makes N injective and
h(z)=-sum_j N_j z has bounded sublevel intersections with Q: each N_j z is then
bounded above and below. A sufficiently distant cap Q_T has old vertices and
new horizon vertices, with the horizon disjoint from R. Qualitative compact
polytope graph connectivity gives one old-to-horizon edge [p,z]. Discard the
auxiliary path used to find it. Join x to p using <=D old bounded edges and
append this one edge. Stop at the first new cut equality.

Every preceding step survives as an R-edge. The first crossing edge intersected
with R is the nontrivial prefix ending at that first equality. Restriction of
an extreme face to a smaller convex parent preserves extremeness, so this
prefix is an R-edge and its new endpoint is a vertex. Tied cuts are harmless.
No diameter of a cap or cut face is paid or assumed.

## 3. Target-bound locking creates small excess

At a target vertex v the columns A_T for its strictly interior coordinates are
independent. Otherwise a small plus/minus kernel displacement supported on T
would contradict extremeness. Hence t<=r.

At a current vertex x, keep fixed every target-bound coordinate already equal
to v. This defines a face R of P containing both endpoints. Eliminate all
coordinates identically at box bounds on R, including those forced implicitly.
They agree with v. The remaining M-coordinate section has equation rank r'<=r
and dimension q=M-r': because no box bound is universal, averaging strict
witnesses supplies one point strict in all remaining bounds. Interior coordinates
fixed by equations are accounted for by r'.

Now remove only the still-unmatched target-facing bounds: for v_i=0 delete the
lower bound but keep z_i<=1; for v_i=1 delete the upper bound but keep z_i>=0.
Keep both bounds on T. The resulting Q is pointed because every coordinate
retains at least one finite bound. It is full-dimensional in the same equality
affine space and is described by M+t inequalities. Thus

    e=(M+t)-(M-r')=r'+t<=2r.

All deleted inequalities are strict at the current x, so x remains an old vertex.
If x!=v a deleted bound must remain: otherwise independence of A_T forces x=v.
That bound's plane meets the section at v. Parts 1 and 2 reach a first new target
bound in at most binom(2(r'+t),r'+t) edges. Lock the newly met bound(s), and repeat.
These edges lie in a face of P, so they are P-edges.

Each phase strictly increases the set of fixed target-bound coordinates and
none is ever released. There are at most s(u,v) phases. Replacing every r' by r
proves the asserted bound. Once all target bounds agree, A_T independence fixes
all remaining coordinates too. This is not a circuit route or an unknown
shortest-distance charge; actual steps have been constructed.

## 4. Consequence for repair costs; exact limitation

If K actual repair faces have certified affine box-section models with <=M
coordinates and rank <=r, their intrinsic budgets sum to at most

    K M binom(4r,2r).

The existing distinct-region theorem adds the number E of explicitly supplied
surviving edge supports. For actual Cartesian-product models, add factor budgets;
the exponential need only use the largest individual factor rank.

If overall size is N>=2, K<=N^a, M<=N^b, r<=c log_2 N, and E<=N^g, then the
total repair budget is at most N^(a+b+4c)+N^g. Thus logarithmic coupling rank,
not just fixed rank, is a quantitatively sufficient geometric certificate.
No claim is made that the general projective/circuit supports have it.

A generic n-slack embedding of a d-polytope has consistency rank n-d. At balance
n=2d that rank is d, so this gives an exponential bound, not Polynomial Hirsch.
Low effective coupling rank cannot be inferred from a generic representation
or from small face dimension. The formal circuit-to-edge frontier is unchanged.

The repository's verified one-sum box-slice theorem is sharper for its rank-one
case; this result is not claimed as an improvement there. Primary related
literature Dadush--Koh--Natura--Vegh, Mathematical Programming 206 (2024),
DOI 10.1007/s10107-024-02107-x, concerns circuit diameter of box/equality systems,
not a proof of this ordinary-edge result. Priority and best-known status have
not been established.

## Executed exact checks (not Lean)

The standard-library Fraction constructor enumerates vertices and actual edge
rays, chooses common-face edge steps by strict exposed-objective descent, clips
at the first target equality, and verifies all emitted final edges and budgets.
BFS is used only AFTER construction to measure comparison distances.

Main suite: 24 instances; 21 all-ordered-pair small instances and 3 selected-pair
larger instances; 985 total enumerated vertices; 4,047 constructed ordered pairs;
9,171 locking phases; 2,834 phases using an actual clipped ray; 11,626 output edge
occurrences; 2,819 auxiliary models. All routes meet their phase and pair bounds.
All 21 small final vertex sets and edge graphs are independently reconstructed,
and 365 auxiliary vertex sets are re-enumerated via full active-bound systems.
The selected larger models have (m,r,vertices)=(7,3,37),(8,2,154),(10,2,575),
with 66 ordered pairs each. These are not all-pairs claims.

Additional normalization tests check graph isomorphisms and all 53 ordered pairs
in three nonuniform/zero-width box controls. Appending dependent/zero equations
preserves the base model's entire route hash. Coefficients above 10^30 are tested.
The final complete verifier reproduced both saved JSON outputs byte-for-byte.

Reproduction in the supplied standalone packet:

    bash scripts/verify_rank_box_cost.sh

The packet includes the full exact source, selected explicit paths, per-phase
budgets, input matrices, hashes, and a verification receipt. Its executable
source is distributed in that packet; this repository note is the complete
mathematical handoff, not a claim that the tests are present on this branch.
