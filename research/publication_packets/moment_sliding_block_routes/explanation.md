# Explicit consecutive-block routes in the original moment system

## Exact new result

`Hirsch.moment_sliding_block_original_routes` constructs a whole finite route;
it does not accept a route or a list of feasible vertices as an input. Let a be
any strictly increasing real sequence on the natural numbers. Only its first m
terms are used in the original inequality system. For positive k with 2k<m,
put d=2k and define the original mean-centered rows

    A_i(x)=sum_(j=1,...,d) [a_i^j - (sum_(l<m) a_l^j)/m] x_j,
    P={x : A_i(x)<=1 for every i<m}.

For any nonnegative s,L with s+L+2k<=m, the theorem proves L<=m-2k and constructs
an INJECTIVE function p on Fin(L+1) such that:

* Every p(t) is an actual Mathlib extreme point of P and is feasible.
* The exact tight original labels at p(t) are s+t,...,s+t+2k-1.
* Every successive segment [p(t),p(t+1)] is an actual Mathlib IsExposed subset
  of P. Since p is injective these are nondegenerate original edge segments.
* For every original row, the times at which it is tight form an interval.

The input s,L specify which consecutive-block vertices to construct, not a
supplied short walk. The bound on label positions ensures the windows fit in
the available original rows; it does not assume geometric feasibility or edge
existence. L=0 constructs one actual vertex. k=0 is excluded deliberately: then
sliding labels cannot define a nondegenerate edge. The public hypothesis is a
strictly increasing sequence on all natural numbers, not an arbitrary unordered
finite parameter map. The construction and numerical tests use only the prefix
in the statement; no claim about an unproved extension operation is required.

This is a CLASS of routes through explicitly identified consecutive-block
vertices, not an all-pairs diameter theorem for arbitrary moment vertices or
arbitrary polytopes. For fixed k,m, selecting s=0 and L=m-2k gives m-2k+1
distinct vertices joined by m-2k genuine original edges. Other moment vertices
can have separated pairs of tight labels; the theorem does not route them into
this chain. It does not prove shortestness of every subpath.

## Polynomial construction, not an optimizer or a rank oracle

For a block starting at r, form the polynomial

    q_r(T)=product_(j=0,...,k-1)
        (T-a_(r+2j)) (T-a_(r+2j+1)).

Its degree is exactly 2k because every factor is monic. At any indexed parameter
a_i, each adjacent pair is nonnegative: either i is at or below the lower
index, or i is at or above the upper index. There is no integer index strictly
between consecutive indices. Thus q_r(a_i)>=0 for every original row. Strict
monotonicity also proves that q_r(a_i)=0 exactly when r<=i<r+2k.

Let h_r=(sum_(i<m) q_r(a_i))/m. At least one original index is outside the block,
because 2k<m, so h_r>0. Write c_j for the coefficients of q_r and define

    p_r(j)=-c_(j+1)/h_r,  j=0,...,2k-1.

The unchanged accepted coefficient-centering identity yields

    A_i(p_r) = 1 - q_r(a_i)/h_r.

Therefore p_r is feasible with exactly the desired block tight and every other
row strictly slack. The proof gives this identity for every original inequality;
it never changes the average to the block average. It uses no optimization,
supplied support point, determinant, vertex enumeration or inverse oracle.

The accepted moment vertex theorem gives extremality because exactly d rows
are tight. The d-label block at r and the block at r+1 share exactly d-1 rows.
The accepted #295 theorem then identifies their entire common supporting slice
with the closed segment and proves its exposedness. Its exposing functional
is the sum of those original common rows, not an auxiliary projected objective.

The route is p(t)=p_(s+t). The first tight original label determines its block
start, so distinct times give distinct vertices. Finally, for a fixed label i,
tightness is the arithmetic condition s+t<=i<s+t+2k. If it holds at two times,
it holds at every time between them. Nonrevisiting is derived from this explicit
construction, not imposed as a global-polytope premise.

## Reuse and scope relative to the Polynomial Hirsch project

The complete namespace prefix from ACCEPTED #295 is reused byte-for-byte up to
`end Hirsch.MomentEdges`, excluding its old public solution and axiom-print
suffix. Accepted proof2e5a27346baa0c00f5329bcb6e8c44a67278281a, theorem
d727e34d-b52e-4bfa-8291-947010b1f130. The original verified ZIP and all five frozen
file hashes were independently checked. Its constructive moment-vertex and
finite-margin dependencies are actual proof bodies, not newly stated axioms.
No accepted public target is registered or submitted again.

#295 alone provided a conditional edge theorem: actual feasible vertices with
one tight-row exchange define an original edge. The NEW work constructs those
vertices and the exchanges throughout a counted finite route. The mathematical
route uses the classical paired-root structure of cyclic polytopes; no historical
novelty or improved best cyclic diameter estimate is claimed. The repository's
#267 direct packed-block experiments are prior related work. Maksimenko's2009
paper gives a stronger classical cyclic-polytope diameter result.

For m=4k+1, taking s=1 and L=2k constructs a route from the block1,...,2k to the
disjoint block2k+1,...,4k. The tests execute this in dimensions8/16/32/64. These
are the same kind of short original routes relevant to the full-flagification
size obstruction, but this theorem does not itself assert that obstruction,
formalize a minimum-distance lower bound, or prove all-polytope route existence.

The next broader interface would handle multiple separated adjacent pairs and
prove a counted sequence of legal block moves, or use another original-edge
construction for arbitrary carriers. Supplying a combinatorial path as an
unproved hypothesis would not close that gap. The current theorem does not
pretend to do so.

## Verification boundary

The originating runtime has no Lean/Lake executable. A fresh DNS check for
GitHub/raw/toolchain hosts failed. The existing requested PR-comment workflow
is the prepared final compilation/axiom/publication gate; no new workflow,
permissions, token, Mathlib pin or trusted-publisher secret split is introduced.
The source is not called compiled until that actual gate succeeds. A failed
compiler result must be preserved, not treated as a mathematical disproof or
hidden by changing the public hypotheses.

The proof is self-contained, with an import/open/settings-only preamble and an
inlined public target signature matching `theorem solution`. Five transitive
axiom printouts are requested. The inherited helpers are not self-imports of the
target. Source inspections and rational tests are explicitly NOT Lean verification.
Only the real publisher receipt can establish acceptance. Do not repeat a
publication command while an earlier request is unresolved.

## Executed independent rational tests

The producer multiplies the root polynomials. The small independent references
instead solve every original square active-row system using rational Gaussian
elimination. Nine models examine2014 such systems, yielding255 vertices and687
edges;1759 infeasible full-tight solutions remain excluded. The full constructed
corridors total30 original edges. Each edge's common-row objective is evaluated
on EVERY reference vertex,1437 evaluations total, and has exactly its two
endpoints as maximizers. Interior checks have exactly the common rows tight.

Among85 pairs of corridor vertices, SIX contiguous subpaths are longer than
independent BFS shortest paths. These adverse cases are retained. The whole
2D/eight-row corridor uses6 edges while its endpoints are only2 edges apart.
Thus the new theorem is not a shortest-path algorithm or a benchmark-improvement
claim. It certifies the route that it constructs.

Sixteen assorted subcorridors include zero-length paths, nonzero starts and
nonuniform rational parameters. Four larger explicit original-H tests through
dimension64 verify every row identity and strict interior tight set WITHOUT
building the full original graph or a refined complex. Twenty-one saved
consumers replay with polynomial/witness production disabled. Eleven malformed
or out-of-domain cases are rejected. An odd-degree polynomial with roots2,3,4
has opposite signs at nodes0 and6; this explains the even-dimension restriction
rather than silently applying it outside its hypotheses.

    python3 scripts/test_moment_sliding_block_routes.py

Reports and the complete fixture regenerate. Clean replay/source identities
are supporting software records, not platform receipts. Python/JSON is not
Lean-extracted. No native library, credential or font is part of the bundle.

Sources:
- Accepted #295 packet, research/publication_packets/moment_common_row_edges/.
- A. Maksimenko, The diameter of the ridge-graph of a cyclic polytope,
  Discrete Mathematics and Applications19(1),2009,47--53,
  DOI10.1515/DMA.2009.003. Used for attribution, not as an unproved import.
- Mathlib at pinned revision c5ea00351c28e24afc9f0f84379aa41082b1188f,
  Polynomial monic product degrees and finite-set cardinality.
