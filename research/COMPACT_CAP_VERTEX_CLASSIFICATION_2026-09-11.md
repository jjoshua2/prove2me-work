# Compact cap vertex classification: remove the ray-enumeration dependency

Date: 2026-09-11. Repository: `jjoshua2/prove2me-work`.

## Evidence boundary and active work

This continuation supplies a complete ordinary mathematical argument, two full
Lean candidate modules, and an executed exact rational regression suite. The
Lean modules have **not been compiled or kernel-audited**. They contain no
intentional proof holes, but absence of holes is not verification. No Prove2Me
API call, submission, registration, or publication was made in this continuation.
No novelty or literature-priority claim is made.

The working runtime had no Lean/Lake installation; direct GitHub access failed
DNS resolution, and attempts to fetch the pinned Lean release failed. Therefore
no speculative Actions compiler loop was started. Run the supplied local gate
under the committed Lean v4.30.0 / Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f` environment before merging.

The repository was rechecked before writing: another continuation has opened
PR #145, `formal/recursive-or-rigid-carrier`, concerning the equal-excess carrier
split. This package is an independent cap-geometry line, does not modify that
PR or its verifier, and should remain one draft until its own gate passes.

## 1. Stronger local classification, with a shorter proof

Let

    Q = {x in R^d : a_i.x <= b_i, i=1,...,n},
    R = Q intersect {x : c.x <= M}.

Assume only that R is compact. Then every vertex z of R is either a vertex of
Q, or satisfies

    c.z = M,
    there exists v in Vert(Q) with c.v < M and [v,z] an edge of R.

No assumption that Q is bounded, full-dimensional, simple, or irredundantly
presented is needed. No recession-ray classification is needed. In particular,
**the cap does not need to be beyond every old vertex for this local theorem**.
An old vertex can be excluded by the cap without invalidating this statement.

### Proof

A vertex strictly below the cap was already a vertex of Q: any segment of Q
through it can be shortened locally while remaining strictly below the cap.
This is the existing checked `HirschCut.strict_cut_extreme_to_parent` lemma.
Thus a new vertex z satisfies c.z=M.

Let I be the old constraints tight at z, and let

    W = {g : a_i.g=0 for every i in I}.

The cap functional is injective on W. Indeed, if g is also annihilated by c,
then g annihilates every active constraint of the capped H-presentation at z.
The checked finite-perturbation theorem
`HirschPolynomialAccess.vertex_tight_rows_span_checked` forces g=0.
This is the entire rank argument; a separate dimension/ray library is unnecessary.

Consider the compact old-active face

    F = {x in R : a_i.x=b_i for every i in I}.

It is a closed convex extreme face of R and contains z. It also contains some
y with c.y<M. To see this, use non-extremeness of z in Q to write z as a strict
convex combination of distinct outer points u,w. Every old row active at z is
tight at both u and w. Neither endpoint can have cap value M unless it equals z,
by the kernel injectivity just proved. Since their strict convex combination
has cap value M, one endpoint lies strictly below M and belongs to F.

Minimize c.x over compact F and choose a minimizer v. Then c.v<=c.y<M.
For any x in F set

    t = (c.x-c.v)/(M-c.v).

The minimizing and cap inequalities give 0<=t<=1. The point
p=(1-t)v+t z has exactly the same cap value and old active-row values as x.
Consequently p-x lies in W and is annihilated by c, hence p=x. Therefore

    F = [v,z].

The endpoints are distinct. Since F is an extreme face of R, [v,z] is an actual
edge, not a circuit segment or an exterior shortcut. Its endpoint v is a vertex
of R strictly below the cap and hence a vertex of Q. This proves the claim.

### Why this helps formalization

The earlier ordinary argument classified the old active face as an unbounded
ray and excluded the bounded-edge alternative using a far cap. The new argument
works entirely inside the already-compact truncation and proves precisely the
adjacency needed by the exterior-cap witness theorem. It avoids formalizing
rays, their endpoints, and the classification of one-dimensional unbounded faces.

## 2. The global cap level must preserve all old routes

Local adjacency is not the whole witness. To transport an arbitrary old graph
route of length D, the cap must preserve every old vertex/edge used by that route.
A uniform sufficient condition is

    M > max(c.v : v in Vert(Q)).

PR #144's proved level was chosen beyond the original bounded parent P, not
necessarily beyond all vertices of its deletion outer Q. Its statement is valid;
it simply does not yet supply this stronger old-route preservation hypothesis.

### Exact genuine-facet counterexample to the parent-only shortcut

Take

    P = {0<=x,y<=1, x+y<=3/2}.

Encode the two lower bounds as -2x<=0 and -2y<=0; encode the upper bounds as
x<=1 and y<=1. All five parent inequalities are genuine, indispensable facets.
Delete x+y<=3/2. The outer Q is the unit square, and its explicit negative-row-sum
cap functional is exactly c.(x,y)=x+y.

The level M=7/4 is strictly beyond all of P, since max_P(x+y)=3/2. Nevertheless,
it excludes the old outer vertex (1,1), whose cap value is 2. Thus containing
the whole parent does not imply containing every old outer vertex, even for an
irredundant parent presentation. This is a gap in that prospective inference,
not a counterexample to PR #144 or to the local classification.

### Repair without enumerating all row bases in Lean

Every finite H-polyhedron has finitely many vertices. Map a vertex to its full
finite set of tight row indices. If two vertices have identical tight-row sets,
their difference annihilates every row active at the first vertex. The checked
active-kernel theorem forces equality. The coding map is injective into the
finite powerset of the row set, proving vertex finiteness.

For compact nonempty P, the union P union Vert(Q) is compact. Maximize the cap
functional on that union and add one. This gives one level strictly above both
the entire final parent and every old outer vertex. PR #143 supplies boundedness
of the explicit deletion cap at this or any other finite level; closedness gives
compactness. Old vertices and old bounded edges now all survive.

## 3. Candidate implementation

`Solutions/PolynomialCompactCapVertexClassification.lean` supplies the finite
vertex coding argument, cap-active kernel lemma, compact single-cut classification,
far level above a compact set and all outer vertices, and old vertex/edge survival.

`Solutions/PolynomialOneRowDeletionCapWitness.lean` specializes these results to
the existing `deletionCappedOuter` and `deletionCapValue`. Its proposed theorem
`HirschCapVertices.exists_deletion_cap_with_vertex_classification` bundles:
compactness; strict separation from the parent and all old outer vertices;
exact recovery on reinserting the deleted row; preservation of all old vertices
and edges; and the new-cap-vertex/old-neighbor classification.

For finite coding only, the deleted row is represented by 0<=0. That redundant
row is **not** used to claim a row-count saving. Use the existing genuine
`Fin.succAbove` deletion model for excess arithmetic.

## 4. Executed exact evidence

Run from the repository root:

    python3 scripts/check_cap_vertex_classification.py --output /tmp/cap-vertex-exact.json

The standard-library Fraction suite enumerates every full-rank row basis for
both outer and capped models. For each new cap vertex it constructs an actual
neighbor by moving inward along the one-dimensional old active kernel until an
old row blocks. The output verifies feasibility, old-vertex membership, strict
cap inequality, preservation of every original active row, and exact edge rank.
It does not merely compare numerical diameters and does not use BFS to find
the claimed neighbor.

Results: 129 instances; 735 outer-vertex occurrences and 824 capped-vertex
occurrences; 193 constructed new-cap/old-neighbor certificates; 754 old edges
preserved across 100 strict-far instances; 29 additional instances excluding
old vertices. Counts across different instances are occurrences, not distinct
geometric objects globally.

Controls include empty caps, dimension zero, embedded rays/segments, a nonsimple
square cone, redundant and zero rows, a cap through some old vertices, and
coefficients above 10^35. Seeded families cover dimensions 2, 3, and 4. These
finite regressions are not universal proof or Lean hull formalizations.

Two successive executions produced byte-identical full JSON reports. SHA-256:

    084a002e8c4447edf73bfd665e93ef90d9e5d7338b1cb99fbf6fa7b0d4229a0c

The compact committed summary records that hash; the full report is reproducible
from the script. Python byte-compilation and shell syntax checks also passed.

## 5. What remains after the geometry is checked

Run:

    bash scripts/verify_cap_vertex_candidate.sh

This first reproduces the exact report/hash, then compiles both candidate
modules and explicitly audits the ten principal declarations. Repair any Lean
elaboration/API failures locally; use the repository's shared final verification
path afterward. Keep the PR draft until actual compiler/axiom evidence exists.

After that, port/apply the historical exterior-cap routing assembly to current
main's inner-product-based clipping API. Its historical module uses different
radial/continuous-linear-map interfaces; do not blindly import obsolete ancestry
or claim that the current candidate already proves the full diameter transfer.

There are still TWO independent cost obligations:

1. `LowerExcessHpolyDiameterBound` quantifies only over **bounded** nonempty
   H-polyhedra. It cannot be applied to the unbounded deleted outer Q just because
   Q has one fewer inequality. Capping Q adds an inequality again; counting that
   artificial row restores the parent row count. A new bounded-to-pointed
   transfer or a different amortized/structural argument must pay the outer cost.
2. The final blocker face can retain the parent's row excess, so its graph budget
   is not automatically supplied by scalar-excess induction either.

Even a complete D+1+B geometric clipping theorem would remain conditional on D
and B. Do not relabel these costs as solved or register another equivalent Open
child. The point of this continuation is to remove a genuine geometry obstacle
while making the still-missing cost argument harder to overlook.
