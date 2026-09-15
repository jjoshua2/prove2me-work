# Target-deleted phase counting: cyclic bounds, quadratic tails, and the remaining exponential obstruction

## Status, provenance, and scope

This is a written mathematical deduction and exact computational research. It
is NOT a new Lean proof, Prove2Me acceptance, or proof of Polynomial Hirsch.
The classical Upper Bound Theorem (UBT) is an explicit external ingredient.
No claim of historical priority is made for truncation, vertex counting,
cyclic face numbers, or known low-dimensional diameter estimates.

The actual #253 selector and its original-row auditor are unchanged. The
new code consumes their completed route certificate, constructs analysis-only
counting caps, and verifies the transport. It does not choose new neighbors or
run a new pivot policy. The separately authored #255 same-anchor shortening
was present in the live queue and was not copied or modified. Its hidden-target
family is reused below WITH attribution as a boundary test, not invented again.
#244/#250/#238 retain their separate assigned work.

Input class: a simple, bounded, full-dimensional d-polytope P with m genuine
original facet inequalities a_i x<=b_i and vertex endpoints u,v. With redundant
input rows, the larger row count remains a valid, weaker bound. This is not
a theorem for arbitrary nonsimple image presentations. Set e=m-d. Exactly d
facets contain v; call their index set T. There are exactly e non-target rows N.
If u and v share d-r facets, simplicity gives r<=e.

## 1. All vertices before a phase acquisition survive target deletion

A phase has a fixed set J of acquired target facets. In the affine space

    H_J={x:a_j x=b_j for j in J},    h=d-|J|,

the current phase vertex x0 has exactly h further active rows K, all in N.
These rows are independent on H_J. Use their original slacks as coordinates:

    z_i=b_i-a_i x, i in K;    x=x0+D_K z,

where the already-audited original inverse columns satisfy a_i D_j=-delta_ij.
Now DELETE every unlocked target inequality, but KEEP the equalities in J:

    Q_J={x in H_J:a_i x<=b_i for i in N}.

This is an h-dimensional polyhedron with at most e inequality facets. It may
be unbounded or have nonsimple vertices. We do not assume otherwise.
In the z chart its K inequalities are precisely z_i>=0. Every other retained
row has strict slack at x0. Thus a sufficiently small all-positive z is a
strict feasible point: full intrinsic dimension is preserved.

Let y be ANY original vertex in the phase BEFORE its first new target-facet
acquisition. Its exact active set is J union K_y, with |K_y|=h and K_y subset N.
Those remaining rows still have independent rank h on H_J. Therefore y is a
vertex of Q_J, not just a feasible point in a relaxation. In particular ALL
pre-acquisition route vertices survive, including intermediate polygon vertices
rather than only decision anchors. The target itself need not survive, and
we never count it as a vertex of Q_J without proof.

This is the opposite deletion from historical #165/#169: those keep target-tight
rows to preserve the TARGET and can lose other old vertices. Here the unlocked
TARGET rows are removed, specifically to preserve the pre-acquisition vertices.
No historical batch-reinsertion theorem is republished or presumed to transport
graph distances. This difference in which rows survive is essential.

## 2. One finite cap permits a classical cyclic-polytope count

Consider any finite prefix of pre-acquisition vertices. Set

    R=1+max_prefix sum(z_i).

The capped polytope

    Qbar_J=Q_J intersect {sum(z_i)<=R}

is compact, since z>=0 and sum(z)<=R. It is full-dimensional, since sufficiently
small positive z is strict in all inequalities, including the cap. It has at
most e+1 facets, and the cap is STRICT at every counted vertex. The h old
independent active rows therefore preserve each vertex exactly.

The choice of R may depend on the prefix and actual coefficients; its magnitude
never appears in the combinatorial count. This is not a conditioning claim,
a bound on rational bit sizes, or a cap needed by the route producer. It also
is NOT a projection: the existing path continues to consist of original edges.
We use the auxiliary polytope only to COUNT already-certified original vertices.
No short auxiliary path is substituted for an original one.

Let U(M,h) be the classical maximal number of vertices of an h-polytope with
at most M facets. Polarity and McMullen's UBT give the cyclic formulas

    U(M,2k)   = binom(M-k,k)+binom(M-k-1,k-1),
    U(M,2k+1) = 2 binom(M-k-1,k).

These apply to arbitrary capped polytopes, not only simple ones. The cap can
create degenerate or extra vertices outside P; such vertices only consume
part of the upper bound. The tests deliberately exercise both phenomena.

## 3. The phase bound includes its final acquisition edge

Loop-erase one completed phase, giving original vertices x0,...,x_L. Before
x_L no new target row is tight; at x_L at least one is acquired. There are
exactly L pre-acquisition vertices x0,...,x_(L-1). They are distinct vertices
of the capped polytope just constructed. Consequently

    L <= U(e+1,h).                                           (1)

The right side is NOT U-1: the terminal acquisition point was deliberately
excluded from the preserved-vertex count. The statement needs no objective
progress or bound on polygon choices once the finite phase is supplied.
For #253 the fallback arcs themselves are strictly increasing, but acquisition
arcs can decrease the phase objective. Loop erasure handles any possible
repeated intermediate vertices honestly. The new bound is for the delivered
loop-erased route, not automatically for every raw committed trace.

Phasewise erasure preserves all locked target facets. Different phases cannot
share an earlier pre-acquisition vertex: a newly acquired target row is strict
at every earlier point of that phase and remains tight forever afterward.
Thus phasewise erasure is the same as global chronological erasure, apart from
shared phase junctions. This is explicitly checked against #253's returned
loop-erased path, rather than silently changing its output.

This phase lemma applies to any FINITE target-locking original-edge route.
For the particular complete-two-face rule, the final retained polygon route,
including its last edge, is shortest and costs at most a=floor((e+2)/2).
We may therefore sum (1) only in dimensions h>=3:

    L <= a + sum_{h=3}^r U(e+1,h), r>=2;   L<=r for r<=1.      (2)

No short-phase hypothesis is inserted. The algorithm's existing finite
termination gives the route; target deletion and UBT bound the resulting path.

## 4. This gives quadratic four- and five-face tails, not only a planar tail

The first cyclic terms are

    U(e+1,3)=2e-2,
    U(e+1,4)=(e+1)(e-2)/2,
    U(e+1,5)=(e-2)(e-3).

Hence (2) yields

    r=3: L <= 2e-2+a,
    r=4: L <= (e+1)(e-2)/2 +2e-2+a,
    r=5: L <= (e-2)(e-3)+(e+1)(e-2)/2+2e-2+a.                (3)

These are intrinsic retained dimensions, not ambient restrictions. This
improves the counting account for the actual algorithm, not its selected
path and not the best known classical low-dimensional diameter bound.

For comparison with the last #254 weighted bound (not merely older #253):

| excess e | initial r | #254 bound | new bound |
|---:|---:|---:|---:|
|12|4|367|94|
|12|5|1089|184|
|12|12|8223|976|
|20|20|2097215|46353|
|29|3|192|71|
|29|4|4267|476|
|29|5|31687|1178|

These are theorem-bound comparisons, NOT newly observed route lengths. The
32-facet three-dimensional corridor still has the SAME 23-edge route and
20-edge shortest distance; its guaranteed count is now71, not192 or480.
No claim that an accounting improvement itself changed a path is made.

## 5. The all-dimensional sum is Fibonacci, so still exponential

With F_0=0,F_1=1, the cyclic formula gives exactly

    sum_{h=1}^e U(e+1,h)=F_(e+4)-3.                           (4)

One derivation uses sum_k binom(n-k,k)=F_(n+1). The odd-h terms sum to
2 F_(e+1)-2*[e even]; the two even-h sums are respectively
F_(e+2)-1-[e odd] and F_e-[e odd]. Their sum is
F_(e+2)+2F_(e+1)+F_e-3=F_(e+4)-3. This is an all-parameter identity,
not an extrapolation from the tests through e=100.

Since r<=e, (2) implies for e>=2

    L <= F_(e+4)-e-6+floor((e+2)/2).                          (5)

Thus the previous full binomial inventory can be replaced by a Fibonacci-type
count, asymptotically O(phi^e), phi=(1+sqrt(5))/2. This is exponential, NOT
polynomial. It is also NOT a claimed improvement of the best general diameter
bound: classical quasipolynomial existence bounds are asymptotically better
in the regime relevant to the general conjecture. The point here is an
unconditional better count for this SPECIFIC certificate-producing strategy.

For h>=3, cyclic facet/ridge incidence gives
h*U(M,h)=2*f_(h-2)(C(M,h))<=2*binom(M,h-1), so U(M,h)<=binom(M,h-1).
This also directly compares (2) with the older subset sums, without trusting
finite numerical tests as a universal inequality proof. Taking the minimum
with any separate independently valid route bound is always permitted.

## 6. Why counting every target-deleted vertex cannot finish Polynomial Hirsch

Reuse #255's already-authored family

    0<=x_i<=1,
    sum(x)+x_i <= d+a_i,  a_i=1/2+(i+1)/(10d^2).

Its designated target is tight on all d new rows and strictly satisfies every
cube row. Deleting the target rows leaves the EXACT d-cube: e=2d inequalities
and 2^d vertices. Thus the inventory of relaxed vertices is genuinely
exponential in e, not just inflated by the cyclic bound.

Likewise, fix d-2 cube coordinates to zero/one, with at least one zero. The
whole resulting square strictly satisfies every new target row, because its
maximum sum(x)+x_i is at most d<d+a_i. It remains an original two-face, disjoint
from all target facets. There are

    binom(d,2)*(2^(d-2)-1)

such squares, each of weight q-1=3. Therefore a bound on ALL target-free polygon
weights is also exponentially large. This is an inventory obstruction, not
an exponential lower bound on the number of faces actually SELECTED. #255
already supplies short routes on this family. No hidden-target construction,
route formula, or classical pivot lower bound is claimed new here.

The next global argument must therefore control which relaxed vertices or
retired faces the algorithm actually visits, exploit structure, or use a
different route family. Counting the entire cap, despite this improvement,
cannot alone become a universal polynomial potential.

## 7. Executed exact validation and reproducibility

The two test stages execute644 routes and1826 original edges in the unchanged
#253 rule. All644 happened to have no loop removals; this empirical fact is
NOT used to assert raw-route bounds universally. The delivered ledger checks
1574 phase caps and9875 restricted inverse identities. Original reference
checks cover634 endpoint pairs on11 independently enumerated small graphs;
nine nonshortest routes are retained. Five stacked corridors and three
intrinsic-three-face embeddings have their explicit separate construction
checks and are not claimed to have fully enumerated high-dimensional graphs.

The high-dimensional models include centered moment-curve polars in dimensions
4 and5, distinct clipped non-product moment-polars, and #255 hidden targets
through dimension6. The original graph is independently enumerated only in
the stated small cases; no complete graph is supplied to the route producer.
All input facet claims in these finite models have original relative-interior
anchors or their explicitly checked construction.

Thirty-two counting caps are independently enumerated through1519 active
subsets:296 cap vertices, including96 outside the original target cuts and
four degenerate caps. Every counted original route vertex persists. These are
exact extra tests of the cap argument, not a proof that the caps are simple.
Twenty-six saved audits pass with inverse/basis production and polygon tracing
disabled. Nine malformed or omitted-data cases fail. The Fibonacci identity
and improvement inequalities are additionally checked for all e<=100.
Full target-free square counts are checked only through d8. Larger exponential
counts follow from the displayed formulas, not claimed enumeration.

    python3 scripts/test_target_deleted_phase.py --stage low
    python3 scripts/test_target_deleted_phase.py --stage high
    python3 scripts/target_deleted_phase_accounting.py input.json route.json --output account.json

The test reuses four byte-identical dependencies already on main, including
#254's construction helpers. Producer/JSON/UBT are not Lean-extracted. The
source manifest and execution summary are derived local records, not platform
responses. Full reports and generated fixtures are in the conversation bundle
and regenerate with the commands above. No Actions verification or theorem
registration is requested for this research-only contribution.

## Primary sources and remaining scope

P. McMullen, *The maximum numbers of faces of a convex polytope*, Mathematika17
(1970),179-184, DOI10.1112/S0025579300002850:
https://londmathsoc.onlinelibrary.wiley.com/doi/10.1112/S0025579300002850.
This is the explicit external UBT ingredient, not a new result from our tests.

J. Pfeifle and G. M. Ziegler, *On the Monotone Upper Bound Problem*:
https://arxiv.org/abs/math/0308186. Classical vertex-count versus monotone-path
issues should not be confused with a new polynomial path theorem here.

M. J. Todd, *An improved Kalai-Kleitman bound for the diameter of a polyhedron*:
https://arxiv.org/abs/1402.3579. The present exponential strategy bound does not
improve that classical quasipolynomial general existence estimate.

The genuinely new repository interface is the finite target-deleted cap ledger
for already-certified ORIGINAL routes and its sharper quantitative account.
No assumed short phase, weakened simple-polytope hypothesis, fake edge transport,
or new general Polynomial Hirsch solution is supplied. The accepted Lean chain
and all concurrently owned work remain unchanged.
