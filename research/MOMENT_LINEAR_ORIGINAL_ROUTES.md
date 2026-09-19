# A full linear-length original-edge route for the moment family

## The exact result

Let d<m and let a_0<...<a_(m-1) be arbitrary real parameters. In the ORIGINAL
space R^d define

    A_i(x)=sum_(j=1..d)(a_i^j-(1/m)sum_z a_z^j)x_j,
    P={x: A_i(x)<=1 for every original i}.

The new proof constructs a route between ANY TWO actual extreme points u,v of
P with at most 2(m-d)+1 nondegenerate original edges. Every visited point is
extreme. Each consecutive closed segment is an exposed and extreme subset of
P and equals the ENTIRE feasible slice where every original inequality common
to its endpoints is tight. No auxiliary projection, feasible-vertex list, parity
oracle, rank certificate or short exchange sequence is assumed.

This is the complete geometric composition after the order-only #306/#307 work,
not another theorem conditional on the missing geometry. It retains negative
root-polynomial normalization, arbitrary real gaps, odd and zero dimensions,
and coincident endpoints. The number m is the represented original row count;
the theorem does not additionally assert irredundancy in every boundary case.

## From arbitrary extreme points to legal selected sets

For every d-label set S form the monic polynomial q_S(t)=product_(i in S)(t-a_i)
and its mean mu_S over ALL m original nodes. Its coefficient candidate is
v_S(j)=-coeff_(j+1)(q_S)/mu_S. The complete numeric catalogue proves that
mu_S!=0 and q_S(a_i)/mu_S>=0 for all original nodes characterize exactly the
actual extreme points, with active labels exactly S and no duplicates.

The nonzero values of q_S have one common sign exactly when every two nonroot
labels have an even number of roots between them. This proves equivalence
between the complete scalar test and the selected-set Gale predicate. It also
derives nonzero mean; the proof never assumes mu_S>0. Thus every arbitrary
endpoint supplies an actual legal selected set, not merely a supplied special
consecutive block or separated adjacent-pair configuration.

## Bounded label walk and actual geometry at every step

Write r=m-d. The complement of a Gale-even selected set has an increasing
enumeration h_i with h_i mod2=(b+i) mod2 for b=0 or1. The exact count of selected
labels below h_i gives C_i+i=h_i; even selected gaps give constant parity of
C_i. The accepted order-only proof packs each endpoint to its parity anchor
in at most r single-label moves. The anchors {0,...,r-1} and {1,...,r} differ
by ONE label. Concatenation and deletion of stationary steps give at most
2r+1 genuine exchanges while preserving Gale evenness throughout.

For every intermediate selected set, the same complete parity catalogue
produces an actual extreme point of P, retaining ALL original inequalities.
A single selected-label exchange leaves exactly d-1 common tight rows. The
accepted original-H common-slice theorem proves that their entire equality
slice is the closed segment joining the endpoints, exposed by the sum of the
common original rows. The two points are distinct because their exact active
sets differ. This is the missing transfer from combinatorial exchanges to
original polytope edges, proved for the whole walk and arbitrary endpoints.

## Reuse and independent verification boundary

The full source retains the accepted #299 root-catalogue prefix, #295 edge
namespace and #307 route bodies unchanged. The MomentEvenGaps namespace from
#302 is also unchanged. That PR's four substantive helpers had standard-only
axiom reports, but its old public wrapper failed; we exclude that wrapper and
DO NOT claim #302 itself accepted. The whole combined source is compiled and
axiom-audited as one distinct original-geometric target. No unproved old public
theorem is imported as an assumption. See the new packet's actual evidence for
its own compilation/publication result, rather than inferring it from reuse.

## What this does not prove

This moment family has strong special order and interpolation structure. The
proof does not assert that arbitrary polytope normals have it, or that an
arbitrary polytope can be moved into this family while preserving its original
edges and row budget. Therefore it is not unrestricted Polynomial Hirsch.
It is not an optimal classical diameter result: sharp cyclic-polytope results
predate this project, including A.M. Maksimenko, The diameter of the ridge-graph
of a cyclic polytope, Discrete Mathematics and Applications19(1),2009,47-53,
DOI10.1515/DMA.2009.003. No historical-priority claim is made.

The constructed walk need not be shortest, vertex-simple, nonrevisiting,
target-locking or monotone for the sum of target rows. A nondegenerate exposed
segment is what each step certifies. The proof is noncomputable real mathematics,
not a verified executable rational algorithm or parser. Generalizing the method
requires a real geometric transfer or a larger class with a proved substitute
for the order property; simply assuming Gale evenness on arbitrary active sets
would reintroduce the central gap.

## Executed supporting checks

Twenty-eight complete small models (all0<=d<m<=7) use independently solved
original-row square systems, not a supplied vertex list. All247 systems recover
125 vertices. Every one of913 ordered endpoint pairs is routed:2960 original
edge occurrences,25223 original-row identities and1366 negative-mean visits.
All195 distinct graph edges have their common-row supporting objective checked
against every reference vertex, totaling1672 comparisons.

The test compares independent shortest distances and retains660 nonshortest
routes,224 repeated-vertex walks and584 target-row-loss walks. No stronger
property is inferred. Four selected larger cases in d8 and d16 check original
feasibility and exact active/inverse/common-rank certificates on paths of
length1,9,1,17; their full graphs are not enumerated. Eleven saved records
containing36 edges are replayed with label routing, candidate/polynomial
construction and square-system solving disabled. Six forged inputs fail.

A clean four-script workspace reproduces the complete12677-byte report and
324763-byte fixture byte-for-byte. The three existing helper scripts remain
unchanged in the repository and accompany the standalone bundle. These tests
are separate from Lean verification.

    python3 scripts/test_moment_linear_original_routes.py --out /tmp/moment-linear
