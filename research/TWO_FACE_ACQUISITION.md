# Complete two-face acquisition and retirement of improving faces

## Scope, provenance, and the actual advance

Continuation from main `6d9dac0a5f0192759a35448de6919b2de5925a73`, after the
merged target-roof barrier #251 and target-acquisition phase selector #252.
This is written mathematics and exact rational research software, NOT a new
Lean proof, Actions verification, or Prove2Me acceptance. The existing accepted
#250 projected-image face-locking theorem and its owner's implementation are
unchanged. This code works in SIMPLE, bounded, full-dimensional ORIGINAL-H
polytopes. It does not transfer a source-polytope edge through a projection.

The main new ingredient is to explore complete original TWO-DIMENSIONAL FACES,
not an ever-larger ball in the graph. A two-face polygon has at most m-d+2 edges,
and at a current h-dimensional retained target face there are binom(h,2)
incident two-faces. Thus one decision can inspect arbitrarily long graph arcs
at polynomial cost in the original input dimensions, without d^h unrestricted
lookahead. Actual explored corners are charged separately from committed edges.

There is also a quantitative accounting theorem. When no inspected two-face
contains a new target facet, move to the best phase-objective value over all
those faces. Each such fallback permanently retires at least h-1 improving
two-faces. Distinct labels give the explicit bound in Section 5. It remains
exponential when dimension and facet excess grow together, so it DOES NOT prove
Polynomial Hirsch or improve the best known general diameter estimate.

The positive result is not just another selector without a count: its work is
charged to original non-target facet subsets. The remaining obstacle is that
there can be exponentially many such subsets. For affine products of polygons,
fallback is unnecessary and the rule is shortest, without a supplied chart.

The exact old scripts used as dependencies are unchanged:

- simple_tangent_policy_audit.py, blob73dc32b9753d7d0fe5e67ca1f4fad0534b6b1976;
- target_phase_pivot.py, blob4b6be3e8f7fc304c87474205898d85f71e39a15d;
- target_roof_phase_barrier.py, blob87c82480b19b3c699d2c9bcf1919d3bb8ea16058.

The new producer itself needs only the first dependency. The other two are
unchanged comparison/fixture code. No workflow, pin, secret or prior proof changes.

## 1. Original two-faces have a small, complete certificate

Let P={x:A_i x<=b_i}, i=1,...,m, be a simple bounded full-dimensional polytope
in dimension d. For the facet-count interpretation use an irredundant original
H-description. With redundant strictly inactive rows the same bounds remain
valid in the larger input-row count, not a falsely reduced facet count.

At a simple vertex x there are exactly d active rows I. Their matrix T is
invertible. Its negative inverse columns D_j satisfy T D=-Id and generate the
whole tangent cone. Releasing one active row and following its column to the
minimum positive original-row slack ratio gives the complete incident edge.
The other d-1 independent active rows remain tight, so this is an ordinary edge,
not a circuit step, a feasible diagonal, or an edge of an extension.

For distinct r,s in I, fix I\{r,s}. Their intersection with P is a genuine
2-face F: simplicity makes its local tangent dimension two, and its remaining
constraints cut out a bounded polygon. Every edge of that polygon is supported
by at least one original row outside the fixed d-2 rows. One supporting line
cannot give two different polygon edges, since its intersection with a convex
polygon is a single face. Hence

    f_0(F)=f_1(F) <= m-(d-2)=e+2,   e=m-d.                  (1)

The certificate gives the entire cycle in a deterministic original-row order.
At each supplied vertex it checks the original inverse identity, every original
inequality, and that the two allowed rays lead exactly to its predecessor and
successor. There are no repeated vertices. Every cycle edge has a distinct
additional original-row label. These tests prove the length bound and complete
cycle coverage. The polygon graph is connected, so a closed component with both
neighbors covered cannot omit another boundary component. No adjacency oracle,
LP, inverse, or rank routine is called by this checker.

Let v be the target and T_v its d active rows. At x keep J=I intersect T_v locked.
The retained face P_J has dimension h=d-|J|. Its incident two-faces correspond
EXACTLY to pairs of unlocked active rows, so there are binom(h,2). Every such
face fixes J and remains in P_J. Their fixed-row labels are unique in a simple
polytope: a 2-face has exactly d-2 containing facets.

This is not a general claim of polynomial vertex enumeration. In dimension two
one explored face is the whole original polygon; in larger dimensions the
producer enumerates only incident polygon boundaries. It is not given an ambient
graph or precomputed global vertex list. Boundedness and simplicity are the
stated input class, not inferred for all unseen vertices from one basis.

## 2. A target-acquisition macro with bounded original-edge cost

Use #252's target-slack phase normalization. At a phase anchor p let
J=T_v intersect active(p), and put

    f_p(x)=sum_{j in T_v\J} A_j x/(b_j-A_j p).               (2)

This objective is fixed until the phase's first new target equality. All its
coefficients are positive. In P_J the unique maximizer is v, and the initial gap
is h. At a later x, the exact tangent identity

    v-x=sum_{j in active(x)} (b_j-A_j v) D_j

uses zero coefficients on J and positive coefficients on every unlocked active
row. Applying f_p proves that at least one allowed edge strictly improves f_p.
This is existence of an improving edge, not a lower bound on its gain.

First inspect every allowed incident edge. If a one-edge new target-facet
acquisition exists, use it; no two-face exploration is needed. Ties follow
completed phase gain and target-slack ratios, just as in #252.

Otherwise trace every eligible two-face. Walk both orientations from x and stop
each at its first vertex with a previously missing target row. Among all such
first-hit arcs choose one of minimum length, then use phase gain and the ordered
target-slack signatures for ties. The shortest arc to any fixed polygon vertex
has at most floor(f_0(F)/2) edges. Thus every selected acquisition costs at most

    a = floor((e+2)/2).                                     (3)

The macro can DECREASE f_p, even on its first edge. Its progress is permanent
acquisition, not monotonicity of an unrelated old objective. The entire arc is
verified on original inequalities, keeps all J rows tight, and ends precisely
at its first new target equality. That equality is locked in the next phase.
There are at most r=d-|J_initial| acquisitions. Simplicity gives one new active
facet per edge, though only the upper bound is needed in the accounting.

Every non-backtracking two-edge path in a simple polytope lies on one of its
incident two-faces: the intersection of its two common edge-row sets leaves
d-2 independent fixed original rows. Therefore the new search includes every
radius-two acquisition that #252 could find. This is a containment of LOCAL
options, not a theorem that the entire greedy trajectory is never worse.

## 3. Fallback to an actual polygon maximum, not one more local pivot

If no eligible two-face has a new target-facet vertex, every one is disjoint
from every missing target facet. Indeed a nonempty intersection of the compact
polygon with a supporting target hyperplane is a polygon face, and contains
at least one polygon vertex, which the complete trace would have found.

At least one allowed incident edge improves the fixed f_p. When h>=2 it belongs
to an inspected polygon. A linear functional on a convex polygon increases
strictly along a boundary arc until its first maximizing vertex, unless it is
constant on the polygon. A zero edge at the maximum is harmless: use its first
endpoint. There cannot be a zero edge below the maximum obstructing both uphill
arcs, because an edge perpendicular to the objective is supporting, hence lies
at an extremal value. Thus the best objective over the inspected polygons is
reachable along one of the enumerated strictly increasing prefixes.

Choose such a prefix with the largest endpoint objective value; break equal-value
ties by shortest prefix then invariant signatures. Its length is at most e+1.
Each committed fallback edge strictly improves f_p. The endpoint dominates EVERY
vertex of EVERY polygon inspected at that decision, not just its chosen face.
The auditor verifies this dominance explicitly.

There is no fallback when h=1: the remaining segment reaches the target directly.
There is no fallback when h=2: the retained target face itself is one of the
complete polygons and contains v. For h>=3 it may genuinely occur; Section 7
provides an explicit simple-polytope example, so it is not a discarded edge case.

## 4. Each fallback retires at least h-1 improving ORIGINAL two-faces

Call an inspected face improving at anchor x if its maximum f_p exceeds f_p(x).
Take an improving incident edge. In the simple h-dimensional retained face it
belongs to exactly h-1 incident two-faces: pair its released row with any other
unlocked active row. All those distinct faces are improving. Therefore every
fallback has at least h-1 improving face labels to charge.

At its chosen endpoint z, f_p(z) is at least every inspected face maximum. Future
fallback anchors in the SAME phase have strictly increasing f_p. An already
charged face can never be improving again at one of those anchors. Inspecting
it again is allowed, but it cannot receive another improving-face charge.

After a phase ends, at least one new target row j is locked. Every polygon
inspected during any earlier FALLBACK was disjoint from all then-missing target
facets, including j. It therefore cannot intersect any later retained face.
Its label cannot be charged in a later phase either. This distinguishes a
permanent combinatorial charge from an arbitrarily rescaled numerical gain.

The software keeps a global set of charged d-2-row face labels. It verifies
that each fallback contributes at least h-1 previously uncharged improving
labels and that its endpoint dominates all inspected face maxima. This set is
AUDIT evidence, not an additional route-selection oracle or a free global graph.

## 5. An explicit original-facet bound, and exactly why it is not Polynomial Hirsch

Fix one phase with target equalities J and dimension h. At a no-acquisition anchor,
every active row outside J is outside T_v. There are only e=m-d non-target rows
in the entire original input. Every eligible 2-face has fixed rows

    J together with h-2 non-target rows.

There are at most binom(e,h-2) possible labels. By Section 4, if B_h is the number
of fallbacks in that phase, then

    (h-1) B_h <= binom(e,h-2),    h>=3.                     (4)

There is at most one phase at each h; acquired target rows never disappear.
Consequently the entire COMMITTED ordinary-edge walk has the explicit bound

    L <= r floor((e+2)/2)
         +(e+1) sum_{h=3}^r floor(binom(e,h-2)/(h-1))
      <= r floor((e+2)/2) + sum_{j=2}^{r-1} binom(e+1,j).    (5)

The last equality of coefficients uses
(e+1) binom(e,h-2)/(h-1)=binom(e+1,h-1).
Empty sums cover r<=2 and the equal-endpoint case. Since a source's r unlocked
active rows all lie outside T_v, r<=min(d,e). A coarse alternative is

    L <= r floor((e+2)/2) + 2^(e+1)-e-2.                    (6)

This proves finite termination without assuming a short phase or appealing only
to the total finite number of vertices. Decision anchors cannot repeat: within
a phase fallback values strictly increase, and across phases a new target
equality excludes old anchors. Acquisition prefixes can in principle revisit
non-anchor intermediate vertices, so the output also provides chronological
loop erasure; each surviving edge remains an original edge and length can only
fall. No such repetition occurred in the executed suite.

The bound is polynomial for FIXED r (or has a fixed-excess interpretation), but
is exponential when r and e grow together. Fixed-dimension/excess regimes and
better general diameter bounds already exist in the project and literature.
This is a bound for THIS explicit selector, not a newly best general diameter
bound or a solution of Polynomial Hirsch. Its useful information is that the
uncontrolled fallback work has been converted to a precise supply of original
facet-subset charges. Further work must control that supply more efficiently or
find a stronger reusable charge; simply calling the binomial sum polynomial
would be wrong.

Per decision, at most binom(h,2)(e+2) polygon-corner occurrences are inspected.
Every inverse, slack ratio and point can be computed with rational elimination
and arithmetic in polynomially many bit operations in the rational H-input
size: vertex/basis coordinates are ratios of original-row minors, and objective
coefficients/slack ratios inherit polynomial bit-size bounds. This is a
PER-DECISION statement, not a polynomial bound on all decisions. Certificate
size likewise counts repeated face occurrences; cached producers do not erase
their costs from verification.

## 6. Shortest routing on affine products of polygons, with no factor chart supplied

For P=P_1 x ... x P_s with polygon factors, each original 2-face is either a whole
polygon factor with all other factors fixed, or a rectangle formed by one edge
in each of two factors. In a rectangle, any new target-facet acquisition must
already be accessible on an incident edge in the corresponding factor. Thus,
when there is no immediate acquisition, rectangle faces cannot improve the
first-hit distance; the algorithm uses an arc in a complete polygon factor.

In a polygon, acquiring a target facet means reaching the target or one of its
two neighbors. If no target facet is shared, the shortest first-hit arc to the
two target neighbors followed by the retained target edge is a shortest route
to that polygon's target. If a target facet is already shared, the remaining
edge goes directly to its target. Once acquired, target rows stay fixed. Every
committed edge changes one factor, and every such change lies on a shortest
cycle arc for that factor. The total length is therefore

    sum_i dist_cycle(P_i)(source_i,target_i),

the exact product-graph distance. No fallback occurs. This proves shortestness
for all endpoint pairs in this class, not just the displayed test endpoints.
The classical product graph fact is not new; the certificate-producing rule
finds these paths using only A,b and endpoints, not a supplied decomposition.

Invertible affine changes and positive row rescaling preserve complete face
cycles, acquisition distances, phase-objective gains and target-slack ratios.
All tie comparisons use these ratios with fixed original row-label order.
Thus the whole trajectory is affine-equivariant and row-scale invariant.
Arbitrary row-label permutations can change ties; that invariance is not claimed.
An affine hidden product remains covered without knowing its chart.

## 7. Positive comparisons and retained counterexamples

The #252 fixed-horizon polygon inserts h vertices before a backward target exit.
Its depth-two acquisition rule takes N+1 edges when that exit is beyond its
horizon. The complete two-face rule explores its whole polygon (linear in its
number of ORIGINAL facets) and takes the shortest h+2-edge route instead.
It is not an O(d^h) graph-ball expansion disguised as a polynomial operation.

Executed examples include N64,h2:69 genuine facets, 65 old depth-two edges versus
4 new edges; and N64,h16:83 facets, 65 old edges versus18 new edges. The latter's
first acquisition is17 edges away, yet it is found by tracing83 polygon edges.
The traced edges are counted, not confused with the18 committed route edges.

Products of15-gons in dimensions4,6,8,12 have225,3375,50625,11390625 vertices and
30,45,60,90 original facets. The new routes have12,18,24,36 edges, all shortest.
They inspect7/22/50/161 two-faces and61/154/310/875 face-edge occurrences. The old
radius-two comparator is freshly run at dimensions4/6/8 and takes18/27/36 edges.
The old comparator in dimension12 exceeded the short local tool-call budget;
NO old dimension12 route count is reported. The new dimension12 route is fully
executed and audited. A six-dimensional hidden affine product with varying
polygon sizes has a shortest13-edge new route versus15 for the old comparator.
No full high-dimensional product graph is constructed.

The truncated octahedron |x_i|<=2, +/-x_1+/-x_2+/-x_3<=3 gives a genuine no-access
case: at u=(2,1,0), target v=(-2,-1,0), all three two-faces through u are disjoint
from all target facets. A fallback is necessary. Its executed route has6 edges,
matching independent BFS. This prevents promoting the positive polygon examples
to a universal one-decision-per-phase claim.

A clipped slanted prism over a parabolic polygon supplies non-product-looking
local geometry beyond pure polygon products; no affine-product classification
is needed for its tests. It is explicitly generated by 0<=z<=1+x/3 and the cut
x+y+z>=1/5. On81 selected endpoint pairs the old depth-two rule uses408 edges,
the new rule358, and shortest paths353. Five new routes remain nonshortest.
This is exact graph comparison, not a universal improvement guarantee.

## 8. Actual execution, independent checks, and formalization boundary

The eleven independent ORIGINAL-H reference graphs have182 vertices,312 edges,
and102 genuine facets (each with a strict relative-interior witness). The six
original #252 model definitions are retained, with all614 ordered distinct pairs;
five additional graphs use80 deterministic sampled pairs each, plus two explicit
hard pairs, totaling1016 pairs.

- Existing depth-two rule:2562 committed edges,33 nonshortest routes.
- New complete-face rule:2506 committed edges,16 nonshortest routes.
- Sum of independently shortest distances:2490.
- Relative to depth-two:21 improved pairs,995 ties,0 worsened in THIS sample.
- The six original models have NO improvement: both totals1230 versus1228 shortest.
  The observed gains arise in the longer polygon and clipped-prism holdouts.

There are2084 independently checked decisions,344 complete face-vertex-set
comparisons and2824 traced face-edge occurrences. Every face certificate is
compared to ALL reference vertices satisfying its fixed rows. Its shortest
first-hit arc is checked by independent restricted-graph BFS, as is inclusion
of every depth-two acquisition. Seven fallback decisions retire21 previously
uncharged improving faces. Fifty-six committed edges decrease the old phase
objective. No loop erasure removed an edge in these runs.

Six delayed-polygon cases, five product cases and four roof cases add15 complete
new routes. The roof comparisons freshly run the unchanged #252 depth-two rule
in dimensions3/4/6/8; both it and the new rule use d edges. The exponential #251
canonical trajectories are explicitly FORMULA-ONLY comparisons in this turn,
not claimed to have been replayed by these tests.

Nine affine transformations and nine row scalings preserve the entire new route.
Nine certificate audits succeed with inverse/basis/face/discovery functions
replaced by functions that raise exceptions. Nineteen malformed, forged,
nonsimple or capped cases are rejected. Zero-edge and one-dimensional routes
are included as boundary checks. Larger product distances come from their
proved combinatorial product construction, not a full graph oracle.

All stages bind the exact new source and all three unchanged dependencies.
Full fixtures and detailed pair tables regenerate deterministically. The staged
runner permits each graph/product case to execute separately; assembly rejects
mixed source hashes. Numerical tests are NOT Lean proof terms and the Python
parser/producer is not kernel-extracted. No new Lean module, theorem submission,
workflow or permission change is made in this research continuation.

## Reproduction

    python3 -m py_compile scripts/two_face_acquisition.py scripts/test_two_face_acquisition.py
    python3 scripts/test_two_face_acquisition.py
    python3 scripts/two_face_acquisition.py input.json --output route.json

Input has A,b,start,target only. --certificate re-audits the saved certificate.
Tests support --graph NAME, --family delays, --product-case0..4, --family roof,
--aux and --assemble. Supply a space before the product-case integer.
An edge cap reports an incomplete search, never a negative geometric result.
The archive includes unchanged dependencies for standalone execution; they are
NOT new or modified source in the incremental patch.

## Primary context and next quantitative target

Alexander E. Black, Jesus A. De Loera, Niklas Luetjeharms, Raman Sanyal,
The Polyhedral Geometry of Pivot Rules and Monotone Paths, arXiv:2201.05134,
https://arxiv.org/abs/2201.05134 . Normalized and greatest-improvement pivots and
monotone paths are classical study subjects; no priority claim is made for
all equivalent two-face pivoting or face enumeration variants.

Alexander E. Black, Exponential Lower Bounds for Many Pivot Rules for the
Simplex Method, arXiv:2403.04886v2, https://arxiv.org/abs/2403.04886 . Its
shadow/steepest-edge lower bounds must not be automatically ascribed to this
target-given, potentially nonmonotone acquisition macro rule. Conversely a
favorable finite comparison does not establish a polynomial general rule.

The present all-d argument leaves an exact combinatorial target: replace the
potentially exponential collection of retired original non-target-row subsets
by a polynomially controlled charging object, or prove that only a polynomial
subfamily can arise under a strengthened selector. A constant face-drop count
alone is no longer the argument, but (5) is still not a polynomial in arbitrary
d,m. Existing nonsimple/projected-image work remains separately owned. No
conditional theorem that assumes the desired short phase is published here.
