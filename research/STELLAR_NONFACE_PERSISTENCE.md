# Minimal-nonface persistence obstructs uniformly small full flag refinements

## Status and the change to the research target

This is a written mathematical proof with exact computational checks, NOT a
Lean-compiled or Prove2Me-accepted theorem. No claim of historical priority for
the elementary invariant or a new cyclic-polytope diameter result is made.
The contribution is its precise consequence for the project's current strategy.

The live base was 8f7ae8d325e38b5fce9753a8b7efb995b8a9af5b. It includes #265's
cactus-incidence work and #266's graphical refinement. Those class results,
#261--#264's schedules, and all accepted earlier proofs remain unchanged.
This does not duplicate their planners or add another unproved completion rule.

**Result.** Some rational simple polytopes with m=4k+1 original facets and
dimension d=2k require exponentially many vertices in EVERY flag complex obtained
by a sequence of forward stellar subdivisions of their dual boundary. The
subdivisions may be at ANY faces of size at least two, not just edges, and their
weights may increase, remain constant, or decrease. No choice of macro horizon,
energy, ordering, auxiliary graph, or repeated-incidence schedule evades this
particular full-size obstruction.

On the SAME family, direct genuine original-edge routes have a classical
polynomial construction. The supplied selected endpoints have certified SHORTEST
routes of length exactly d, including a completed 64-dimensional example.
Thus this is an obstruction to a proof strategy's complete refinement size,
NOT a counterexample to Polynomial Hirsch or a lower bound on original diameter.

The ruled-out proposed sufficient step is:

    Every original dual polytopal sphere has a polynomial-size FLAG refinement
    obtainable by forward stellar subdivisions, after which applying the global
    classical M-d bound proves Polynomial Hirsch.

The obstruction does NOT cover arbitrary subdivisions not known to admit such
a forward factorization, inverse stellar moves/coarsenings, unrelated flips,
direct original routes, or a polynomial-length path inside an exponentially
large implicit refinement. Those require their own original-edge transport and
length proofs; none is declared solved here.

## 1. Every old minimal nonface has a distinct minimal descendant

Let K be a finite simplicial complex on m actual vertices; in particular every
singleton is a face. Let E be a face with |E|>=2, and let z be the fresh vertex
of its stellar subdivision K'. Faces of K' are characterized as follows:

* A set T not containing z is a face precisely when T is an old face and E is
  not contained in T.
* A set {z} union U is a face precisely when E is not contained in U and
  U union E is an old face.

For each old inclusion-minimal nonface N, define

    D_E(N) = N                         when E is not contained in N,
             (N minus E) union {z}     when E is contained in N.       (1)

**Claim: D_E(N) is always a minimal nonface of K'.**

If E is not contained in N, N is still absent, and all its proper subsets are
old faces not containing E, hence still faces. If E is contained in N, the
containment is strict because E is a face. The descendant is absent by the
second face criterion. Removing z leaves the old proper face N minus E.
Removing any other descendant label a leaves a z-containing set whose union
with E is N minus {a}, an old proper face; it therefore is a new face. All
one-label deletions are faces, which proves minimality.

This map is injective. Images without z are unchanged; images with z recover
their old preimage by replacing z with E, and the two sorts cannot collide.
Furthermore E itself is a NEW minimal nonface: all its proper subsets remain
faces. E is outside the image of (1), since an old minimal nonface cannot be E
and a changed image contains z. Consequently, writing q(K) for the number of
ALL minimal nonfaces, including pairs,

    q(K') >= q(K)+1.                                               (2)

This statement does not say that the weighted number of HIGHER defects cannot
decrease. A high defect can become a missing pair, which contributes zero to
the older W=sum_high(|N|-2). Its ancestry still exists as a distinct minimal
nonface. Discarding pairs from the budget hid that persistent obligation.

The exact full recurrence used in the checker is the inclusion-minimal family
of E, old N not containing E, and {z} union(N minus E) for every old N meeting E.
Its edge case is imported unchanged from #261. The test also checks arbitrary
face sizes by literal subdivision of maximal simplices, not by comparing the
same recurrence against itself.

## 2. A final flag complex must have room for every surviving root

After t forward subdivisions, every old minimal nonface has a distinct current
descendant, as does the fresh root born at each step. The injections compose.
If the final complex is flag, all these minimal nonfaces have cardinality two.
With M=m+t vertices, it follows that

    q_initial+t <= binom(M,2),      M=m+t.                         (3)

Completeness of the original minimal-nonface list is unnecessary for a lower
bound. If only Q distinct original minimal nonfaces are certified, (3) remains
valid with Q in place of q_initial. This permits an exponential FAMILY of
certificates to be described by a proof, without first enumerating it.

There is an additional original-label interpretation. Assign a singleton
original carrier to each initial vertex, and assign the union of the carriers
of E to each new vertex z. Under (1), the union of the carriers of an original
root's current descendant stays exactly that root N. Thus distinct original
incompatibilities are represented by genuinely distinct final missing pairs;
they are not merged by a favorable schedule.

For integer computation define M_min(m,Q) as the least M>=m satisfying

    binom(M,2) >= Q+M-m.                                         (4)

The code uses exact integer doubling and binary search, never floating roots.
No inverse subdivision is permitted in this invariant: an inverse may remove
vertices and previously persistent roots. Subdivision at a singleton merely
renames a vertex and is excluded from t rather than counted as a birth.

All current nested/block/graphical constructions obtained by ordered stellar
subdivisions are covered, as are arbitrary finite mixtures of the project's
forward edge schedules. The general existence of an arbitrary non-stellar
small flag subdivision is a DIFFERENT question. We do not assume a theorem
identifying every subdivision with a forward-only stellar sequence.

## 3. Exponentially many certified minimal nonfaces in a rational polytopal family

For k>=2 put d=2k, m=4k+1, and

    v(t)=(t,t^2,...,t^(2k)),   t=0,...,4k,
    c=(1/m) sum_t v(t),
    P_k={x : (v(t)-c).x <= 1 for every t}.                         (5)

The augmented moment matrix has nonzero Vandermonde determinants, so the
convex hull of the v(t) is full-dimensional. Each v(i) is exposed by the
nonnegative polynomial (t-i)^2. The positive mean c is strictly interior:
if a supporting affine functional vanished at its positive average, it would
vanish at every spanning vertex. Hence P_k is bounded and full-dimensional,
and every one of its m rows is a genuine facet. A proper supporting hyperplane
of the moment hull has at most 2k roots. Its facets have at least 2k affinely
independent vertices, hence exactly 2k. Thus the hull is simplicial and P_k
is simple. These claims concern original geometry, not sampled local ranks.

Use the 2k odd labels U={1,3,...,4k-1}. EVERY (k+1)-subset of U is a minimal
nonface of the moment hull, equivalently a minimal incompatible family of
facets of P_k. Therefore

    Q_k=binom(2k,k+1)                                             (6)

is a certified lower bound on the number of original minimal nonfaces. The
following direct exact certificates establish both incompatibility and minimality.

### Proper subsets: explicit original-H support points

For any nonempty S with |S|<=k,

    p_S(t)=product_{s in S}(t-s)^2

has degree at most 2k, is nonnegative on every original parameter, and vanishes
exactly on S. Write p_S(t)=sum_j c_j t^j and h=(1/m)sum_t p_S(t)>0. Then

    x_j=-c_j/h,  j=1,...,2k

is an original-H feasible point with

    (v(t)-c).x = 1-p_S(t)/h.

Its active row set is exactly S. In particular every immediate proper subset
of a proposed (k+1)-label nonface has an exact feasible intersection witness.

### The whole subset: an alternating affine circuit

For N={a_0<...<a_k} subset U, adjoin even labels

    Y={a_0-1,a_0+1,a_1+1,...,a_k+1}.

In increasing order z_0<...<z_(2k+2), these parameters alternate Y,N,Y,...,N,Y.
They all lie in 0,...,4k. Set

    w_i=1 / product_{j!=i}(z_i-z_j).

Lagrange interpolation of t^r at these 2k+3 points, followed by comparing its
highest coefficient, gives sum_i w_i*z_i^r=0 for r<=2k+1. The even-position
weights are positive and the odd-position weights negative. Normalize the
positive sum to one; the negative sum is then minus one. This gives equal
convex combinations of the N and Y moment points, with every coefficient strict.

If all original N rows were tight at an H-feasible x, the affine relation would
force all Y rows tight as well. But their union contains at least 2k+1 affinely
independent moment points. A proper supporting hyperplane cannot contain them.
Equivalently, the polynomial (v(t)-c).x-1 would have degree<=2k and 2k+1 distinct
roots, forcing all its coefficients zero, including an impossible constant.
Thus N is incompatible, and the proper-subset witnesses make it minimal.

The checker verifies signs, normalization, every moment identity through 2k,
the original centered-row relation, and the nonzero Vandermonde product. No
floating hull, unproved Gale oracle, or claimed generic LP solve is used for
these certificates.

### Consequence for EVERY forward stellar flag completion

The largest binomial coefficient among the 2k+1 coefficients of (1+1)^(2k) is
binom(2k,k), so binom(2k,k)>=4^k/(2k+1). Since
binom(2k,k+1)=k/(k+1)*binom(2k,k), for k>=1,

    Q_k >= 4^k / (2(2k+1)).

Combining with binom(M,2)>=Q_k gives

    M >= 2^k / sqrt(2k+1).                                      (7)

This is exponential in original dimension d=2k and original facet count m=4k+1.
The H input has O(k^2) rational entries, each of polynomial bit length O(k log k);
the lower bound is not explained by exponentially long input coordinates.
The stronger integer calculation (4) gives:

| d | m original facets | certified Q | every final flag M at least | subdivisions at least |
|--:|--:|--:|--:|--:|
|16|33|11440|153|120|
|32|65|565722720|33639|33574|
|64|129|1777090076065542336|1885253341|1885253212|

These are lower bounds, not constructions achieving those sizes. They do not
assert how many refined vertices a particular path visits. Lower-dimension
parameter values can yield a weak or vacuous lower bound; the table does not
hide that fact as an exact optimum.

## 4. Direct original routes on the same family bypass global flagification

To avoid confusing refinement cost with diameter, the implementation gives an
explicit original-edge route on P_k. This uses classical cyclic-facet combinatorics,
not a new best cyclic-polytope diameter theorem.

A 2k-label facet of the moment hull consists of k disjoint adjacent pairs in
the cyclic order on its m labels. One can read this directly from the sign of
its degree-2k supporting root polynomial: sign-changing gaps must contain no
unselected parameter, including the possible pair across the end of the order.
Equivalently every selected cyclic run has even length. For two facets F,H,
|F union H|<=4k<m, so choose a label absent from both and cut the cycle there.
Each endpoint then consists of k nonoverlapping dominoes on the resulting
4k-position path, with increasing left endpoints a_i and b_i.

Each i satisfies 2i<=a_i,b_i<=2k+2i, so

    sum_i |a_i-b_i| <= 2k^2.                                    (8)

Move left-needing dominoes starting at the first unfinished index, optionally
moving the entire consecutive packed block that also needs left. Then move
right-needing dominoes starting at the last unfinished index, likewise as a
packed block. Neighbor ordering of the target positions prevents crossing.
Each block moves by one position toward its target, and (8)'s progress measure
decreases by the block size. The selected label union of a packed block loses
one outer label and gains one outer label. Thus each move exchanges EXACTLY one
of the 2k active original facets: it is an original edge, not a chain of hidden
pivots, a diagonal, or a projection. This gives for every endpoint pair a direct
route of at most 2k^2=d^2/2 edges. This direct routine is NOT claimed to preserve
all originally common facets for arbitrary endpoint pairs; its selected large
control endpoints have no common original facet.

Every generated vertex has its own degree-2k root polynomial R_F(t), signed to
be nonnegative on all original parameters, and H point x_j=-coeff_j/mean(R_F).
The root Vandermonde rank and the fact that the mean is strictly off the
supporting hyperplane prove independence of the 2k centered active normals.
Adjacent path vertices share 2k-1 independent facets in a bounded simple
polytope, so their segment is a genuine one-face and its endpoints are the
vertices, not just feasible points. The verifier checks all these polynomial
identities and the supplied block-move progress, without searching a graph.

For F={1,...,2k} and H={2k+1,...,4k}, shift the whole packed block right once
per move. There are exactly 2k moves. These endpoints have disjoint active sets;
every original edge leaves at most one of the source's 2k facets. At least 2k
moves are therefore necessary. The route is SHORTEST. The completed exact
k=8,16,32 runs have 16,32,64 original edges, respectively, while their complete
forward flag refinements obey the large table above. Neither an exponential
minimal-nonface catalogue nor the full original graph is enumerated in these
large runs; every actually delivered original vertex and edge is checked.

Maksimenko's 2009 primary paper already gives the exact diameter of cyclic
polars as n-d-max(0,ceil((n-2d)/(floor(d/2)+1))). For n=4k+1,d=2k this is 2k.
Our weaker all-pairs construction and these selected shortest controls are not
claimed as an improvement on that classical result. They make the original-edge
comparison executable and independent of a huge refinement.

## 5. Actual verification and what was not executed

The two new scripts import five unchanged previous scripts, including #261's
complex/edge operation and #266's graphical constructor. The new theorem is
proved directly rather than assumed under a classical paper's name.

* All 114 four-label complexes: 515 literal stellar subdivisions, including77
  at faces larger than edges, with1204 old minimal descendants checked. The
  reference constructs maximal simplices and all their subsets independently.
* 160 randomized multi-step sequences:948 actual subdivisions with ancestry
  maintained at every step. 106 happen to finish flag; no general planner is
  inferred from these random experiments. Four additional simplex schedules
  finish flag. The eight saved full ancestry packets replay exactly.
* All7296 four-label complex/graph pairs from #266:6766 passing graphical
  refinements respect the new count. Negative criteria are not treated as flags.
* For k2/3/4/5:285 distinct minimal-nonface certificates and348 distinct immediate-
  proper-face support witnesses, evaluated against the original H coefficients.
  All60 original moment labels across these four inputs get individual exposure
  witnesses. k8/16/32 additionally have three checked nonfaces and three proper
  faces EACH; all remaining exponentially many certificates are covered by the
  all-parameter proof, not falsely recorded as enumerated tests.
* Independent complete small facet/graph references use all126 and1716 active
  sets for k2/3, yielding27/156 original vertices and54/468 edges. All351 pairs
  in the first graph and120 of12090 pairs in the second are tested. The direct
  route uses1576 edges versus1369 BFS-shortest edges, with110 nonshortest paths.
  It is not a better default. Its selected high-dimensional packed-block paths
  are separately shortest by the source-facet-drop lower bound.
* Fourteen malformed/out-of-scope controls fail, including a forged descendant,
  nonface or singleton subdivision, wrong affine circuit, forged original H
  point, original-edge jump, false progress/block metadata and invalid final
  flag size. Five full route consumers replay with route production disabled.
* Integer lower bounds are verified with exact arithmetic through k80. Their
  exponential growth is proved by (7), not extrapolated from those79 checks.

No long generic stellar-completion run, all possible large schedule search,
large full graph, Lean build, axiom audit, or Prove2Me submission is claimed.
The large cases use explicit family certificates. Python and its JSON parser
are not Lean-extracted or formally verified. Clean dependency replay and byte
identities are preserved separately from these mathematical claims.

    python3 scripts/test_stellar_nonface_persistence.py
    python3 scripts/stellar_nonface_persistence.py --k 32

## 6. Sources and concrete next target

A. N. Maksimenko, *The diameter of the ridge-graph of a cyclic polytope*,
Diskretnaya Matematika21(2),2009,146--152, DOI10.4213/dm1054. The primary abstract
states the exact formula; the English version is Discrete Mathematics and
Applications19(1),47--53, DOI10.1515/DMA.2009.003.
https://m.mathnet.ru/php/archive.phtml?jrnid=dm&option_lang=eng&paperid=1054&wshow=paper

F. H. Lutz and E. Nevo, *Stellar theory for flag complexes*, arXiv1302.5197,
standard forward/inverse subdivision terminology and barycentric construction.
Only this classical background is used; our minimal-nonface invariant is proved
from exact membership. We do not import an assumption that a higher-defect
energy decreases on every arbitrary subdivision.
https://arxiv.org/abs/1302.5197

K. Adiprasito and B. Benedetti, *The Hirsch conjecture holds for normal flag
complexes*, arXiv1303.3598, is the classical M-d theorem used by the earlier
full-flagification pipeline. It is not reproved or submitted here.
https://arxiv.org/abs/1303.3598

The global-total-size route must now be distinguished from path-local work.
A possible continuation can attempt to bound the number of refined labels that
an actual connecting path needs, avoid constructing unused parts of an implicit
refinement, or give a direct original-edge rule outside the full-flag strategy.
The direct cyclic control supplies a regression that such a method should pass.
No bound of that kind is asserted for arbitrary polytopes here. Inverse moves
also escape this invariant but require a new carrier/edge proof; they cannot
silently inherit the forward map. Preserved class results remain useful, while
a universal cheap COMPLETE forward flagification should not be reopened as an
unproved optimistic premise. The Polynomial Hirsch conjecture itself remains
unsettled by this contribution.
