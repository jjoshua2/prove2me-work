# Exact optimal original-row charging, with overload certificates

## Result and precise scope

The input is an arbitrary finite original H-system in R^d, an actual target
vertex v, and N occurrences of genuine nondegenerate original exposed edges
[u_t,w_t] whose endpoints are actual original vertices different from v.
The edges need not be distinct, consecutive, or a path. Repeated occurrences
must remain separate jobs: deduplicating them would change the question.
The body may be unbounded or lower-dimensional. No finite-hull representation,
vertex catalogue, strict exposure, or supporting-row witness is supplied.

The proof derives each edge's full set of available original row labels:

    I = {i : A_i(v)<b_i},
    S_t = {i in I : A_i(u_t)=b_i and A_i(w_t)=b_i}.

Every S_t is nonempty by the accepted original-edge witness from #341. Target-
tight and zero rows cannot enter S_t; redundant or rescaled original rows retain
their distinct original labels. Multiplicities of rows are not silently removed.

For J contained in I, define the forced occurrences

    F(J) = {t : S_t is contained in J}.

The complete candidate derives an optimal integer K and an actual assignment
f(t) in S_t with at most K occurrences assigned to any row. It proves K<=N,
N<=K*|I|, and the exact characterization, for EVERY integer capacity k:

    a capacity-k assignment exists
      iff every J contained in I satisfies |F(J)|<=k*|J|
      iff K<=k.

For every k<K it additionally derives a NONEMPTY original-row set J contained
in I with

    k*|J| < |F(J)| <= K*|J|.

This is an explicit dual overload certificate: all those occurrences have no
allowed label outside J, so no redistribution can fit them into k slots per row.
K and the assignment are outputs, not a favorable-capacity assumption. Empty
edge families and zero row counts are covered; K=0 precisely in the empty case.
The displayed equivalences also imply the closed-form characterization

    K = max_(nonempty J subset I) ceil(|F(J)|/|J|),

with empty maximum defined as zero. The formal statement gives the equivalent
integer inequalities and optimality witness rather than a separate ceil/max
expression.

This is an exact charging theorem for a GIVEN edge family. It does NOT select
that family, construct a short original route, bound K polynomially, or solve
Polynomial Hirsch. A terminal edge incident to v has no positive-slack support
row, so it is deliberately excluded. On a walk reaching v only on the final
edge, charge the preterminal N=L-1 edges; the final edge is accounted separately.
The resulting L<=1+K*|I| is useful only after proving a suitable bound on K along
a constructed route. No such missing bound is made a premise of this theorem.

## 1. Derive labels from original geometry

Reuse the exact accepted finite-margin, tangent-feasibility, exposed-edge-row,
and target-not-in-other-segment proof bodies from PR341. The relevant argument
works for any finite H-system, not only the compact setting of that earlier
public envelope theorem.

An actual extreme target v cannot belong to a segment joining two other feasible
points. Let x=(u+w)/2 on an original exposed segment and choose its exposing
functional f. Then f(v)<f(x). If every row active at x were also tight at v,
the direction x-v would annihilate all active rows. The finite positive slacks
of the remaining original rows allow a small feasible step x+e(x-v), e>0.
Its f value exceeds the maximum f(x), a contradiction.

Therefore some original row is slack at v and tight at x. Since both endpoint
slacks are nonnegative and their average is zero, that row is tight at both
u and w. This supplies S_t.Nonempty for each occurrence without assuming a
neighbor graph, a supporting-row oracle or a chosen basis.

The supporting functional, finite perturbation and whole-segment hypothesis
refer to the ORIGINAL H-body. No edge of a refinement, completion or auxiliary
bipartite graph is substituted for an original edge.

## 2. Necessity of forced-row inequalities

Fix an allowed assignment with every row load at most k. Every occurrence in
F(J) must be assigned to a row of J. Partition F(J) by its assigned row and count:

    |F(J)| = sum_(i in J) |{t in F(J):f(t)=i}|
           <= sum_(i in J) k = k*|J|.

This argument counts occurrences, not geometric edge types. It therefore remains
valid for backtracking and repeated edges and does not assume nonrevisiting.

## 3. Sufficiency via the finite Hall theorem

Make k proof slots for each original row: the slot type is Fin(m) x Fin(k).
An occurrence t can use S_t x Fin(k). For any set E of occurrences, let
J be the union of its eligible rows. Then J is contained in I and E is contained
in F(J), so the assumed row-subset inequalities imply

    |E| <= |F(J)| <= k*|J|
         = |union_(t in E) (S_t x Fin(k))|.

Mathlib's Hall theorem gives an injective slot assignment. Projecting to its
original-row coordinate gives an allowed row assignment. Inside one row fiber,
the second-coordinate slot map is injective into Fin(k), so the load is at most k.
This proves the equivalence, not merely one necessary inequality.

This is the classical capacitated Hall argument; no historical novelty is
claimed for matching theory. The pinned primary source is Mathlib
Mathlib/Combinatorics/Hall/Basic.lean, theorem
Finset.all_card_le_biUnion_card_iff_exists_injective, at revision
c5ea00351c28e24afc9f0f84379aa41082b1188f. It is reused rather than reproved.
The temporary row slots are a finite proof device, not an enlarged polytope
whose edge count is claimed as an original-route bound.

## 4. Derive the optimum and its obstruction

Choose any available label for each occurrence; capacity N always suffices.
The least feasible natural capacity K therefore exists and K<=N. Feasibility
is upward closed. At a capacity k<K the Hall row-subset criterion must fail,
so some J has |F(J)|>k*|J|. J cannot be empty because every S_t is nonempty.
The actual capacity-K assignment supplies the matching upper inequality.
Taking J=I gives N<=K*|I|. No uniform smallness of K is inferred from the least-
capacity construction or from the fact that there are at most m original labels.

This differs from the existing weighted proper-face/shortest-path budget work
(#61) and the convex active-row interval theorem (#185). It optimizes the integral
choice among MULTIPLE labels of each actual edge and derives a certificate of
unavoidable overload. It does not assume an intrinsic face-diameter budget or
repeat the claim that one affine row's active times on a straight segment form
an interval. The remaining geometric problem is to control these forced-row
bottlenecks along a well-chosen original-edge route.

## 5. Executable producer and independent certificate check

A new standalone standard-library script constructs a capacitated bipartite
network with occurrence-to-row arcs and integral capacities. Binary search and
augmenting paths find the least feasible capacity. At K-1, the residual reachable
row set J and its complete forced-occurrence set give the overload certificate.
The certificate consumer does NOT call flow, matching, or optimum search. It
checks actual row eligibility, every assigned load, the complete forced set and
its strict overload inequality. Those two witnesses independently sandwich K.

For geometric inputs, the consumer uses exact Fraction arithmetic. Feasibility
and full active-normal rank certify the actual target/endpoints. Common active
rows have rank d-1, and all original inequalities give the exact supporting-line
interval [0,1], certifying the whole original exposed segment. Rank computation
and JSON parsing are part of unverified Python, not a kernel-certified implementation.

There are no dependencies on the previously blocked radial-envelope supporting
script, no retry of its upload, and no renamed copy of it. The new code was written
for this assignment/overload task. It shares only mathematical notions and Python's
standard-library arithmetic, not that script's producer or consumer implementation.

## Executed tests and adverse examples

The small suite exhausts 2,928 nonempty-eligible-set families, including empty
families, over at most three row labels and four occurrences. Its flow optimum
matches both all row-subset density inequalities and 22,968 explicitly enumerated
assignments. These are finite supporting checks, not the all-input Lean proof.

Eight small original-H models include cubes, simplices, a nonsimple octahedron,
a square pyramid, and an unbounded planar body. Exhaustive original square-system
enumeration checks 843 systems. Together with repeated-edge, dimension-zero,
monotone-cube and Gray-code examples, the small suite audits 63 ledgers and
1,153 edge occurrences. Optimal maximum load strictly improves over the least-
row greedy assignment in 46 ledgers; no improvement is promised for every input.
Nine malformed-certificate or invalid-eligibility controls are rejected.

Four genuinely higher-dimensional tests use the preterminal portions of explicit
short cube walks in dimensions 8,16,32,64. They audit 116 original-edge occurrences;
the maximal loads drop from 7,15,31,63 to 1 while leaving the walks unchanged.
No full high-dimensional vertex or graph enumeration is performed.

The adverse cases are essential. Seventeen copies of one cube edge have only two
eligible rows, forcing optimum 9 rather than 1. An 8D reflected Gray-code walk
ending at zero has 254 preterminal edges; its optimum is 32, certified by the
8-row overload set. That walk's source is ADJACENT to the target, so a one-edge
route exists with no preterminal charges at all. This is an inefficient input
walk, not a diameter or Polynomial Hirsch lower bound. Relabeling cannot repair
an arbitrarily bad route choice. For the pyramid apex target, four base edges
all have one eligible base row and cannot be assigned injectively either.

Clean single-script replays reproduced all FOUR complete report/fixture files
byte-for-byte. Python/JSON and the min-cut implementation are not kernel-verified.
The formal statement is an existence/minimum theorem; no polynomial running-time
claim for the supplied rational geometry checks is made.

## Verification boundary

The complete new standalone candidate imports Mathlib only, has no written
admission or new axiom, and uses a top-level theorem solution matching problem.json.
Its preamble contains imports/open/options only; local definitions appear solely
inside the source and public let expressions. Five transitive reports are requested.
The copied accepted helper declarations have exact source hashes recorded separately.

Local lean/lake/elan and the checked installation/cache paths were absent; the
release and raw toolchain hosts failed DNS. Patch/hash/type checks and executed
Python are not Lean compilation. One carefully prepared complete pinned hosted
gate is requested. Preserve any actual failure and a separate uncompiled repair
rather than performing repeated speculative CI edits. Keep Lean4.30.0, Mathlib
c5ea00351c28e24afc9f0f84379aa41082b1188f, strict reviewed protocol0.10.9, ownership,
allowed actors, duplicate guards and verifier/publisher secret separation unchanged.
