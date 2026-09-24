# Linear original-edge routes under arbitrarily many independent affine roofs

## Exact target and difference from the active exception-count work

Let P be BOTH conv(C), where C is a finite family of 0/1 points in R^n, and the
original m halfspaces D_i x <= b_i. Choose k arbitrary real affine heights
H_j(x)=c_j+A_j x which are strictly positive throughout P. Define the ORIGINAL
body, in R^n times R^k, by

    Q = {(x,y) : D_i x <= b_i for every i,
                  0 <= y_j <= H_j(x) for every j}.

For any two ACTUAL extreme points of Q, this packet constructs a route through
actual extreme points with nondegenerate WHOLE IsExtreme segments of Q. The
length satisfies BOTH L <= n+k and L <= m+k. There are m+2k displayed original
inequalities, so this is linear in the original presentation size, with a degree
independent of k. k is not bounded by a fixed constant. No base graph, vertex
label, complete vertex catalogue, active basis, rank, base walk, or cheap residual
phase is supplied as a public premise.

This is a separate structural application, not a replacement for the owned
few_exception_target_routes packet in #325. That theorem treats arbitrary
exceptional rows without the independent-interval structure; its degree depends
on their number. This packet does NOT prove that an arbitrary polytope has an
affine-roof presentation. It does not modify #325's source, repair, or trigger.
It also does not modify #282's separately owned particular triangular-chain
classification and routes. The base here may be any finite 0/1 hull, including
nonsimple and lower-dimensional examples, not just a cube.

## 1. Derive all actual vertices

For a feasible (x,y), put s_j=y_j/H_j(x). Strict positivity gives 0<=s_j<=1.
For fixed s, the section x -> (x,(s_j H_j(x))_j) is affine and maps P into Q.
If x belongs to a nontrivial positive convex combination of feasible base
points, this section lifts the decomposition to (x,y). Extremality of (x,y)
therefore implies that x is an ACTUAL base extreme point.

Similarly, if 0<y_j<H_j(x), holding all other coordinates fixed and moving y_j
to its two original bounds expresses (x,y) as a strict convex combination of
two distinct feasible points. Thus every roof coordinate of an actual vertex
is either zero or H_j(x). The resulting Boolean roof labels are derived.
Conversely, a base extreme point with all roof coordinates on selected bounds
is extreme: projecting a positive decomposition fixes the base, and equality
at an interval boundary fixes each roof coordinate. This converse is obtained
through the more general full-face lift lemma below.

No assertion about compactness or the completeness of a sampled vertex table
is used instead of this proof. Empty bases have no requested extreme endpoints;
zero base dimension, zero roof count, coincident endpoints and lower-dimensional
bases are retained by the stated quantifiers.

## 2. Genuine horizontal original edges

Fix Boolean choices beta_j. The affine map

    F_beta(x) = (x,(beta_j H_j(x))_j)

lifts EVERY extreme subset F of P to an extreme subset of Q. To see this, project
a positive convex decomposition of a point in F_beta(F). Extremality of F puts
the projected endpoints in F. For a lower-bound choice, a positive combination
of nonnegative roof coordinates is zero, forcing both to be zero. For an
upper-bound choice, use nonnegative affine roof slacks H_j(x)-y_j instead.
Their positive combination is zero, so both endpoints lie on that upper bound.
This proves the entire lifted set is extreme in the original Q.

The affine map carries an ENTIRE base segment to the ENTIRE segment between its
lifted endpoints. It is injective because the first coordinate is unchanged.
Consequently every nondegenerate original base edge gives a nondegenerate whole
original Q edge. This is not inference from a vertex correspondence or projection
of an unrelated extension edge.

## 3. Genuine vertical original edges

The fiber over a base extreme point is an extreme subset of Q: projecting any
positive decomposition fixes the base. In this fiber the heights are positive
constants. Fixing all Boolean roof choices except one leaves a genuine box
coordinate segment. The proof shows the whole segment is extreme, and proves
its endpoints distinct using the corresponding positive height. Extremality
then transfers from the fiber to the original Q.

The finite Hamming induction changes only roof bits that differ from the target,
using at most k original vertical edges. The complete route then follows the
accepted #322 0/1-base route along the TARGET's fixed roof-boundary section. Its
base length is at most n, so concatenation yields L<=k+n. All visited points
are actual Q extreme points by the classification/converse; all segments are
whole original extreme segments by the two geometric arguments.

The Lean theorem supplies these edge constructions and the length bound. It does
NOT assert a complete converse edge catalogue, a graph isomorphism, global
monotonicity, shortestness, or preservation of every previously acquired target
facet. Small exact tests separately check the graph-product correspondence on
all tested vertex pairs; that computation is not a second formal theorem.

## 4. Original inequality accounting

The base dimension bound n<=m is DERIVED from the actual projected source vertex.
The evaluation map z -> (D_i z)_i is injective: if every original row vanishes
on z, both x+z and x-z are feasible, and their midpoint x cannot be extreme
unless z=0. Finite-dimensional injectivity yields n<=m. Therefore the same
constructed route also satisfies L<=m+k, against m+2k original displayed rows.
No rank, full dimensionality, independent row set or irredundant-facet oracle is
assumed. Redundant base inequalities and affine-hull equations are permitted.

The theorem is a restricted original-size result, NOT a solution of Polynomial
Hirsch for arbitrary carriers. Its exact H/hull equality, 0/1-base structure,
independence of roof coordinates and strict positive heights remain explicit.
Arbitrary couplings among the new roof variables are outside this result.
Zero height can collapse two Boolean labels; the tests retain this boundary
example rather than silently extending the vertex-label argument.

## 5. Reuse, provenance and verification boundary

The first 973 lines / 41934 bytes are the EXACT accepted #322 namespace prefix,
from proof 3fa9791c65405c57804730cac7481f28ac26f066. Only its old top-level public
solution and its final print commands are omitted. The new proof invokes its
zero_one_routes helper and finite Route operations; no old public target is
resubmitted. All five dependency-manifest hashes match. Seven final new axiom
prints cover the new chain and root, besides five retained dependency reports.
The registered preamble contains only imports, an open-scoped directive and an
option. Its formal statement exactly matches the new top-level solution type.

The base dimension bound is classical: Naddef's 0/1 diameter result is recalled
in Alexander E. Black, Monotone Diameters of Lattice Polytopes, arXiv:2609.08647
(abstract). General background on deformed product constructions is Raman Sanyal
and Guenter M. Ziegler, Construction and Analysis of Projected Deformed Products,
arXiv:0710.2162 (abstract). Those sources provide attribution/context, not a
substitute for any Lean proof in this packet. No historical-first or best-known
bound claim is made. This simple affine-interval geometry is classical in nature.

Local Lean/Lake were not found on PATH or in the checked default/opt locations;
DNS to raw.githubusercontent.com and releases.lean-lang.org failed. The source
has NOT been locally compiled. Static checks and Python regressions are NOT Lean
verification. This complete candidate is intended for one carefully prepared
normal pinned final compiler/axiom/publication gate. Any failed elaboration must
remain a failure, with a separate reviewed repair rather than speculative repeated
hosted edit/compile runs. No Lean/Mathlib pin, workflow, protocol-version guard,
allowlist, duplicate guard or verifier/publisher credential split is changed.

## 6. Executed exact supporting checks

Thirteen small original-H models include zero-dimensional and zero-roof cases,
a lower-dimensional embedded segment, a nonsimple octahedral 0/1 base, signed
affine coefficients and a 2^-80 height margin. An independent H-reference solves
ALL 554 square active systems (264 nonsingular) and exactly matches all 103
constructed vertices. All vertex pairs are checked against the exact original
edge relation, giving 181 edges. Affine-hull equations are explicitly included
as original paired inequalities in lower-dimensional cases.

The 721 tested endpoint routes contain 1224 edge occurrences, versus 1168 total
shortest-path edges. All 56 nonshortest outputs are retained. The producer uses
the unchanged #322 base-route algorithm and changes roof bits explicitly. Saved
consumers replay with route construction disabled and verify original feasibility,
actual-vertex rank, common-row rank and the ENTIRE support-line parameter interval
[0,1]. Eight malformed small controls and one changed sparse-inverse control fail.
These are supporting exact arithmetic, not Lean-extracted Python or a verified
JSON parser.

Four larger examples with (n,k)=(4,4),(8,8),(16,16),(32,32) verify 120 more original
edges on 16/32/64/128 original inequalities. Each has k independent exceptional
upper target rows, with heights 1+(j+1)*sum_i 2^(-(i+1))*x_i. Each exceptional
row has 2^n+1 values by the WRITTEN formula. The 64D example has 32 exceptions,
4,294,967,297 levels per exception, and an explicit checked 64-edge route.
The large vertex count 2^(n+k) and level counts are formula evaluations, NOT
large-graph enumeration. The sparse original-row inverse certificates check
full row-rank and whole original support segments without large RREF or graph
discovery. No stronger execution or separate family-count Lean claim is made.

Reproduction:

    python3 scripts/test_affine_roof_routes.py --out /tmp/roofs --stage small
    python3 scripts/test_affine_roof_routes.py --out /tmp/roofs --stage controls
    python3 scripts/test_affine_roof_large.py --out /tmp/roofs

The existing test_geometric_coordinate_routes.py dependency remains unchanged.
