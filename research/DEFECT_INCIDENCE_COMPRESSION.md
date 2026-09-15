# Hierarchical incidence compression gives counted flag refinements

## 0. Status, provenance, and the distinct step beyond #260

This contribution is a written mathematical argument and exact research code.
It is NOT a Lean compilation, an axiom audit, a Prove2Me acceptance, or a proof
of Polynomial Hirsch. The input class is simple bounded full-dimensional
polytopes with genuine ORIGINAL facet inequalities. All diameter counts below
refer to their original ordinary edges, not edges of an extension.

The first STATUS read named #259's exceptional-facet confinement. Reading the
actual main commit revealed the other agent's newly merged #260 blockwise
flag refinement, at 2c73c4e10d226b15b09a833468121efbc4cbe4de. That work is reused,
not duplicated: its block refinement supplies our final residual operation,
and its carrier proof motivates the explicit hierarchical transport below.
Its simplex hierarchical illustration and coupled triangle family are already
credited to #260. The new contribution is a SAFE exact stellar update for equal
higher-defect incidences, a bound on the remaining incidence types, and schedules
that handle large coupled defects without an expensive flat block partition.

The classical imported result is Adiprasito--Benedetti's normal-flag Hirsch
bound: a normal flag (d-1)-complex on M vertices has a facet path of length at
most M-d between any two facets. Our argument produces such a same-dimensional
subdivision and transports its path back to original edges. It does not reprove
or republish that classical theorem. Historical priority for every equivalent
form of the parameterized conclusion is not claimed.

## 1. Exact minimal-nonface update for an edge subdivision

Let K be a finite simplicial complex with minimal nonfaces N(K), all of size at
least two. Call a minimal nonface HIGHER when its cardinality is at least three.
In the original dual boundary, these are minimal empty facet intersections.
Let E={u,v} be an actual edge of K and add a new vertex z by stellar subdivision.
The minimal nonfaces of the new complex K' are exactly the inclusion-minimal
members of

    {E}
    union {N in N(K): E is not a subset of N}
    union {{z} union (N minus E): N in N(K), N intersects E}.       (1)

Here is a membership proof, independent of any heuristic nonface update. If z
is absent from a proposed face T, then T is a face of K' exactly when T is an
old face not containing E. If z is present, write T={z} union U. Then T is a
face exactly when U does not contain E and U union E is a face of K. Failure
of that last condition has a minimal witness N subset U union E. If N avoids
E, it is already an old nonface inside U; otherwise {z} union (N minus E)
is contained in T. These alternatives prove that (1) generates every nonface,
and taking its minimal members proves the formula.

An arbitrary edge subdivision can CREATE additional higher defects. For example,
take the join of two triangle boundaries, with higher nonfaces {0,1,2} and
{3,4,5}. Subdividing the mixed edge {0,3} keeps both and introduces {z,1,2} and
{z,4,5}. Thus their number grows from two to four. No unconditional monotonicity
of a higher-defect count is assumed in this work. The exact update is checked
independently by enumerating faces and performing a literal stellar operation
on maximal simplices in the abstract regression.

## 2. A sufficient safe condition: identical nonempty higher incidence

For each current vertex w that belongs to a higher minimal nonface, record

    I(w) = {N in H(K): w in N},

where H(K) is the complete higher-minimal-nonface family. Suppose I(u)=I(v)
is nonempty. Then E={u,v} is an edge: it lies in a higher minimal nonface, all
of whose proper subsets are faces. Every higher nonface contains BOTH endpoints
or NEITHER, so the mixed splitting in the preceding example cannot occur.

Under the subdivision, higher nonfaces update exactly as follows:

    N disjoint from E: keep N;
    E subset N: replace N by (N minus E) union {z},
                 dropping it from the higher list if the result has size two.
                                                                    (2)

To check minimality as well as generation, old missing pairs can only create
new missing pairs. A new pair {z,w} cannot lie inside a higher descendant of N:
that would mean an old missing pair {u,w} or {v,w} was contained in the old
minimal nonface N. Two higher descendants cannot newly contain one another,
because replacing the shared pair by z preserves their inclusion relations.
A descendant pair cannot be contained in another higher descendant for the
same reason. Old higher nonfaces disjoint from E also cannot acquire a smaller
nonface inside them. This proves (2), not merely one direction of an update.

The old vertices u and v REMAIN vertices of the subdivision. They stop appearing
in higher defects; this is not a deletion or identification of original facets.
We add one refined vertex z, rather than changing the original H-polytope.

Let q be the initial number of higher defects and k the size of their union.
Repeatedly subdivide a pair with identical nonempty incidence while one exists.
Each move adds one refined vertex, never increases q, and reduces the size of
the higher-defect support by at least one. If t moves are performed, and q',h
are the terminal higher-defect count and support size, then

    t <= k-h,       q' <= q.                                      (3)

At termination all h nonempty incidence signatures are distinct subsets of a
q'-element set. Consequently

    h <= 2^{q'}-1 <= 2^q-1.                                      (4)

This bounds the RESIDUAL support, even when the original higher nonfaces have
large cardinality or their original union is large. It is not a claim that q
is small on every simplicial sphere. The update and support descent work on
arbitrary complexes; the later route bound additionally uses the dual sphere.

## 3. Complete the refinement and count ORIGINAL route length

After the t safe stellar moves, the current complex has m+t vertices. Refine
its induced subcomplex on the remaining higher-defect support B, |B|=h, by the
single-block barycentric operation already established in #260; leave every
other vertex a singleton block. In each current simplex this is the join of
the barycentric subdivision on its B-part and the unmodified complement.
These subdivisions agree on intersections, so this is an actual subdivision
of the same sphere. In particular it remains pure and normal.

All higher minimal nonfaces now lie in one block. A clique in the refined
complex has its B-vertices in one chain; its other vertices are singleton
labels. If the union were not a face, a minimal nonface would lie in that union.
A higher one would lie in the largest B-chain member, impossible; a pair would
already violate an edge of the clique. Thus the refinement is flag. This is
also a special case of #260's exact at-most-two-block criterion.

Let f_B be the number of NONEMPTY faces of the current induced complex on B.
The final vertex count and original diameter bound are

    M = m+t-h+f_B,
    diameter(P) <= M-d = e+t+f_B-h,       e=m-d.                   (5)

The coarse bound f_B<=2^h-1 gives

    diameter(P) <= e+t+2^h-h-1.                                  (6)

When q>=1, (3)--(4) imply the deliberately loose uniform expression

    diameter(P) <= e+k+2^{(2^q-1)}-1.                            (7)

For q=0 the original complex is already flag and the bound is e. Hence a FIXED
number q of higher minimal nonfaces gives a linear-in-m route bound, regardless
of their sizes. The q-dependent additive term in (7) is doubly exponential,
not a general polynomial estimate. The useful instance count is (5), not this
worst-case simplification. Neither q nor h is declared small without evidence.

### Why all those steps transport to genuine original edges

For a single stellar edge subdivision, a maximal refined simplex F has d
vertices. Its old carrier is F when z is absent, and (F minus {z}) union E
when z is present. A new maximal simplex containing z contains exactly one
of u,v, so its old carrier has exactly d labels and is an old maximal simplex.

Adjacent refined maximal simplices share a ridge of d-1 vertices. If that ridge
omits z its old carrier already has d-1 labels. If it includes z, replacing z
by E produces either d-1 or d old labels. Thus both old carriers have size d
and intersect in at least d-1 labels. They are equal or adjacent old maximal
simplices. The analogous chain-union argument for the final block subdivision
is the established #260 carrier lemma.

Apply these maps backward through EVERY subdivision. An adjacent step remains
an original adjacency or collapses to a stationary step; delete consecutive
equal carriers. Maximal simplices of the original dual correspond to original
vertices of P, and their shared d-1 facets give an actual original edge. Path
length never increases. This is not an arbitrary extension projection.

Compatible endpoint lifts also preserve the smallest original common face.
If E is contained in only one endpoint simplex, remove an E-label absent from
the other whenever possible; when both contain E, remove the same endpoint on
both. The common refined face then carries all previous common original labels.
At the final block step place shared labels first in each chain. Run the flag
segment in the link of that common refined face. All its carriers retain the
original common equalities. The code checks the backward carrier adjacency at
every intermediate level and finally checks every original edge directly using
original inverse identities and its maximal feasible step.

## 4. Sharper schedules for higher-defect incidence patterns

Several patterns eliminate all higher defects without the residual block:

* Pairwise disjoint higher supports N_i: compress each to two labels in exactly
  t=sum_i(|N_i|-2)=k-2q moves. Then M=m+t and diameter<=e+t.
* A sunflower N_i=C union P_i, with nonempty common core C, nonempty disjoint
  petals P_i, and all |N_i|>=3: first compress the common core to one label,
  then each petal to one label. All selected pairs have equal higher incidence.
  The resulting higher defects are pairs, with t=k-q-1 moves.
* At most two higher defects: one needs |N|-2 moves; two disjoint defects need
  k-4; two intersecting antichain defects form a sunflower and need k-3.

These are explicit safe schedules, not a claim to find the cheapest sequence
among all possible stellar refinements. The code uses deterministic twin-pair
choices and verifies all its actual updates. These schedule formulas are tested
on 120 disjoint cardinality cases, 42 sunflowers and 533 two-defect cases.

The simplex boundary is an instructive sanity check but was ALREADY discussed
hierarchically in #260. Its one higher nonface has d+1 labels; d-1 safe moves
give a flag sphere with 2d vertices. Its original diameter is one, not d. Our
contribution does not rebrand that example as new. The generic recurrence and
shared-defect schedules extend beyond that illustration.

## 5. A coupled nonproduct family with large, repeated defect types

The following extends #260's already-known p=2 coupled-triangle family to
p-dimensional simplex factors with p unrestricted. Let p,r>=2, d=pr, and use
x_{ij}>=0 for i=0,...,r-1 and j=1,...,p. Set u_i=sum_j x_{ij}. Impose

    u_i<=1,
    u_i+u_(i+1)<=2-10^{-(i+1)},      i=0,...,r-2.                  (8)

There are m=(p+2)r-1 genuine original facets and e=2r-1. The following proof
justifies the entire class, not just the finite examples.

Start with the product of the p-simplices. Each later cut removes the current
ridge u_i=u_(i+1)=1, which exists by setting other u's to zero; all previous
neighboring cuts are then strict. To prove it is sufficiently shallow, consider
the aggregate u-polytope. Its rows are signed unit rows and adjacent-pair sums.
Alternating column signs and suitable row signs makes the transpose a directed
incidence matrix with a ground coordinate. It is totally unimodular. An elementary
minor proof removes a column with at most one nonzero by expansion; otherwise
each column has one +1 and one -1, giving linearly dependent rows. Thus every
nonsingular square minor has determinant +1 or -1.

Before cut i, all right sides have denominators dividing 10^i. Therefore every
aggregate vertex lies on that rational grid. Every x-vertex has at most one
positive coordinate per block (otherwise vary its split while fixing u). Its
u-image must also be an aggregate vertex: a nontrivial convex combination in u
lifts by keeping the chosen positive coordinate in each block, contradicting
extremality in x. A positive old vertex slack in u_i+u_(i+1)<=2 is consequently
at least 10^{-i}, strictly more than the new cut depth 10^{-(i+1)}.

The cut removes exactly the vertices on that ridge, crosses every incident
outgoing edge strictly, and meets no old vertex on its new hyperplane. This is
a shallow truncation of a codimension-two face of a simple polytope. The old
facets survive and a genuine new facet is created; simplicity is preserved.
Strict feasibility and boundedness also follow directly by choosing all x
small positive and using the nonnegative block sum bounds.

In the dual, the cut subdivides the edge between adjacent upper labels.
Initially the higher nonfaces are the r lower-p-plus-upper sets. Applying (1)
shows that each cut adds exactly two lower-p-plus-cut-label sets, one for each
incident block. They remain minimal: the lower labels lie in no missing pair,
and distinct blocks' lower sets are disjoint. Old upper or cut labels may have
missing-pair interactions, but no such pair lies inside these higher sets.
Hence the final higher-defect list has exactly q=3r-2 sets, each of size p+1.
Its union includes EVERY original facet label.

Within each block, all p lower labels have the same nonempty higher incidence.
Compress them to one representative in p-1 safe moves. Every higher set then
becomes a pair; nothing remains for the residual block. Consequently

    t=r(p-1),     M=(2p+1)r-1,
    diameter(P_{p,r}) <= M-d = (p+1)r-1.                         (9)

This is an ALL-PAIRS structural bound. The final polytope is combinatorially
nonproduct: every original block's higher nonface connects its lower labels
to its upper label, and each added cut label connects the higher incidences of
the adjacent blocks. Their minimal-nonface incidence hypergraph is connected.
A nontrivial Cartesian product would dualize to a join, whose minimal nonfaces
split into disjoint label components. No such split exists. This does not assert
Minkowski indecomposability or difficulty of its actual diameter.

### Why hierarchy improves on flat blocks, not only on a bad heuristic

Every one of the original higher nonfaces here has p+1 labels. In ANY flat
partition satisfying #260's at-most-two-block condition, some block contains
at least ceil((p+1)/2) labels of that nonface. If it contains the whole nonface,
all proper subsets are still faces; otherwise that block piece itself is a face.
Either way, the induced block contains at least

    2^{ceil((p+1)/2)}-1                                         (10)

nonempty faces. Thus every valid FLAT-block refinement has at least that many
vertices. This lower bound concerns the certificate representation, not the
original graph diameter. In contrast our hierarchical count is O(pr), even
when both p and r grow. Taking p=r makes (10) exponential in sqrt(m), whereas
(9)'s refined size and bound are linear in m. This is not a claim that a universal
polynomial flag refinement has now been found.

The p=16,r=2 numerical check uses M=65 rather than at least 511 for ANY valid
flat partition. Its supplied endpoints are only three edges apart, and its
facet excess is three: classical few-excess diameter results already give
stronger bounds there. The useful distinction is the cost of the refinement
certificate, not a claimed record diameter theorem for those endpoints.

## 6. True stalls and why a universal inference would still be wrong

The safe rule requires equal nonempty signatures. A residual antichain can
have all signatures distinct. Abstract q=3 and q=4 examples have h=7 and h=15,
attaining the bound 2^q-1 and admitting no safe move; these abstract examples
are NOT claimed to be polytopal spheres.

Actual polytopal stalls also occur. The polar of the cyclic four-polytope with
seven vertices has seven higher triples, seven distinct support signatures,
and no safe first move. Our final one-block fallback has M=70 and certifies
only 66 edges, far above the observed small distances. With eight facets the
same issue gives M=96 and bound92. These failures are retained in the test
report. More general subdivisions may help, but a mixed pair can split defects,
so the theorem does not silently apply to them.

Nor can one argue that a large defect count makes the original graph hard. The
method is sufficient, not a diameter lower-bound invariant. Its parameter q
may be large on easy inputs, and the final residual refinement may cost too much.
The known exponential lower bound for every ORIGINAL combinatorial segment is
also left intact. We run the classical segment in a DIFFERENT flag subdivision
and map its carriers, which may reenter original facets and leave that restricted
route family. We did not execute the published exponential segment examples.

## 7. Implemented discovery, independent checks, and actual performance

The general producer takes only original rational A,b,start,target. It completely
classifies minimal nonfaces through size d+1 with #258's exact feasible or strict
original-row dual certificates. It then computes safe moves by (1)--(2), builds
the final refined face oracle, runs the unchanged classical segment, and audits
all original edges. It receives no graph or preselected original route.

COMPLETE classification can be exponential and may discover every original
vertex active set. No supplied graph is not the same as no vertex enumeration.
The classification, residual subset and refined vertex caps are explicit. A
cap failure is incomplete work, not a false flag certificate. The supplied-class
route bound is not a polynomial runtime or LP-pivot theorem. Simplicity and
genuine facet presentation are input assumptions, independently verified for
the finite models, not deduced from a handful of local bases.

The consumer validates the original intersection records, recomputes the exact
nonface schedule, and replays link BFS/recursion and the carrier maps. It uses
no geometric optimization or inverse discovery; it still performs graph and
combinatorial computations. Python/JSON has not been extracted from Lean.

Actual completed tests:

* All 114 labelled four-vertex complexes: 438 valid stellar-edge updates compared
  to independent explicit simplex subdivision, 114 safe-twin updates, and 1,110
  adjacent-carrier checks for the pure cases. The abstract inputs are not all
  spheres, so only their local algebra/carriers, not flag-Hirsch bounds, are used.
* Seven original-H reference models give 80 endpoint pairs, with 141 new original
  edges versus 140 for unchanged raw #258 and 140 for independent BFS. One route
  is nonshortest; the method is NOT a benchmark improvement or a new default.
  Their 160 refined edges contract 19 stationary steps. The generic discovery
  performs 1,754 LP maximizations and 5,737 internal pivots. Sampling versus all
  pairs is explicit in each row. Eight saved audits replay with geometric
  producers disabled. Twelve malformed/capped controls are rejected.
* Six coupled-family instances (p,r)=(2,2),(3,2),(3,3),(4,4),(8,4),(16,2)
  verify respectively t=2,4,6,12,28,30 safe moves and M=9,13,20,35,67,65.
  Their all-pairs bounds are 5,7,11,19,35,33. Selected original paths have
  3,3,5,7,7,3 edges. Only the first two additionally receive exhaustive original-H
  vertex/nonface classification and BFS (13 and 25 original vertices). For the
  larger four, the test uses the proved family construction and exact stellar
  history, then audits every delivered edge on the final original inequalities.
  A complete generic LP classification is NOT claimed for those larger models.
* The already-attributed simplex hierarchy is reproduced in dimensions3/6/12/24/32.
  At d32 it has64 refined vertices versus196606 for the optimal flat-block count,
  but the selected original route has one edge and the true diameter is one.

All three stages have been executed and their full reports/fixtures are bundled.
The committed compact summary labels itself derived and binds full reports by
hash. A clean replay uses only two new scripts and three byte-identical existing
dependencies, not a full repository clone. Report timing fields are excluded
from equivalence; every remaining field and full fixture byte must agree.
No Actions, Lean or Prove2Me workflow is triggered for this research contribution.

    python3 scripts/test_defect_incidence_compression.py --stage abstract
    python3 scripts/test_defect_incidence_compression.py --stage geometry
    python3 scripts/test_defect_incidence_compression.py --stage family
    python3 scripts/defect_incidence_compression.py input.json --output route.json

## 8. Literature and exact remaining target

Adiprasito--Benedetti, arXiv:1303.3598, Section3 and the normal-flag theorem,
supplies the short refined path. Lutz--Nevo, arXiv:1302.5197, supplies classical
background on stellar edge refinements and barycentric subdivisions. We derive
and test the exact minimal-nonface update instead of importing an unconditional
nonface-count monotonicity assertion for arbitrary edge subdivisions. In
particular our mixed-edge test explicitly creates additional higher defects.
Labbé--Manneville--Santos, arXiv:1510.07678, gives the exponential limitation for
raw original combinatorial segments, not a lower bound for our different refined
route family. None of these classical results is being claimed as newly proved.

Primary references:
- https://arxiv.org/abs/1303.3598
- https://arxiv.org/abs/1302.5197
- https://arxiv.org/abs/1510.07678

The remaining conjecture-facing obstacle is to control distinct higher-incidence
patterns or permit controlled mixed subdivisions without explosive defect growth.
Neither a bounded number q of original high defects, a short safe schedule,
nor a cheap residual refinement is asserted for arbitrary carriers. The current
step gives an exact safe operation, a parameterized residual bound, and a large
coupled class where a hierarchical certificate is provably much smaller than
any flat block certificate. It leaves the unrestricted geometry explicitly open.
