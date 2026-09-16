# Current Polynomial Hirsch frontier

Repository `jjoshua2/prove2me-work`; updated after merged research PR #267.
Keep Lean `v4.30.0` and Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
Read AGENTS.md, CLOUD_AGENT.md, SKILL.md, CONTINUE_HIRSCH.md and LIVE PR heads/
comments before choosing work. Historical prose is not a fresh platform poll.

The preceding COMPLETE cactus/graphical frontier is preserved verbatim in
[pre-persistence STATUS](https://github.com/jjoshua2/prove2me-work/blob/c6703cfae95ef0952922606aede9c37627a37e93/STATUS.md),
Git blob `73629a62441ef78bee3415a08524af2b0e5cc730`. Its links preserve all
older accepted receipts, research proofs, adverse cases, counts and ownership.
The new contribution is WRITTEN mathematics/exact Python, not Lean compilation,
axiom auditing or Prove2Me acceptance. No publication workflow was requested.

## Objective and a material change in the sufficient strategy

The last preserved authenticated mission audit records root
`58eae2c9-6fd5-4d5d-8aa7-6d552ad80bac` Open and remaining leaf
`Hirsch.common_face_diameter_of_dim_ge_six`,
`87a8b4f4-8b58-4340-8cb9-5fd1b548d01e`, Open. This update is NOT a fresh
root/leaf API poll. The target remains a uniform polynomial ORIGINAL ordinary-
edge bound for arbitrary high-dimensional carriers.

NEW: a universal polynomial TOTAL VERTEX COUNT for complete flagification by
forward stellar subdivisions is not merely an unproved sufficient premise.
#267 gives an explicit rational polytopal family contradicting that premise.
This is NOT a counterexample to Polynomial Hirsch. It does not rule out short
paths in a huge implicit refinement, general subdivisions without a forward
stellar factorization, inverse moves/coarsenings, or direct original routing.
Do not infer a route-length lower bound from this representation-size result.

## Merged #267: persistent minimal nonfaces and exponential completion size

Research head `4170cfca2c6222d5aab52d5d5b7e96f43d01bdc0`;
merge `c6703cfae95ef0952922606aede9c37627a37e93`.
[Full mathematical argument](research/STELLAR_NONFACE_PERSISTENCE.md),
[actual execution report](research/STELLAR_PERSISTENCE_TESTS.json),
[handoff](research/STELLAR_PERSISTENCE_HANDOFF.md), source identities and
clean replay are on main. SEVEN additions, no prior selector/proof changes.

### Invariant for EVERY forward stellar schedule

Subdivide any actual face E with |E|>=2, introducing fresh z. Every old minimal
nonface N has a MINIMAL descendant

    N                         if E is not contained in N,
    (N minus E) union {z}      if E is contained in N.

Checking the proper subsets proves minimality directly from face membership.
Different N have different descendants. E itself is a fresh minimal nonface
outside this image. Thus the total number of ALL minimal nonfaces, INCLUDING
pairs, increases by at least one each forward step. Roots also preserve the
union of their original carriers. The older high-defect W can decrease when
roots become missing pairs; those obligations have not vanished or merged.

After t subdivisions, q original minimal nonfaces and t new roots remain
pairwise distinct. In a flag completion on M=m+t vertices they must all be
missing edges. Therefore

    q+t <= binom(M,2).

A certified SUBFAMILY of q initial minimal nonfaces suffices; complete catalogue
enumeration is unnecessary for the lower bound. The statement includes larger-
face moves, arbitrary order, all energy increases/plateaus and unrestricted
macro horizons. It covers the block/graphical constructions already known to
factor into forward stellar subdivisions. Singleton renamings are not counted
as vertex-adding operations. Inverse subdivisions are outside the invariant.

### Exact rational family and the all-size lower bound

For k>=2 take moment points v(t)=(t,t^2,...,t^(2k)), t=0,...,4k, subtract their
mean c, and define P_k by (v(t)-c).x<=1. It is simple and bounded with d=2k
and m=4k+1 genuine original facets. Each (k+1)-subset of the 2k odd parameters
is a minimal nonface, giving q>=binom(2k,k+1).

Proper subsets have nonnegative squared-root support polynomials, yielding
explicit original-H feasible witnesses. Whole subsets have interleaved even-
parameter affine circuits with strictly signed normalized coefficients; moment
identities and a Vandermonde rank witness exclude a common supporting face.
Simplicity, full dimension and genuine facet rows are proved from the moment
construction, not inferred from a sampled local basis or floating hull.

Since binom(2k,k+1)>=4^k/(2(2k+1)), every full forward flag completion obeys

    M >= 2^k/sqrt(2k+1).

The input rational bit lengths are polynomial in k. Exact integer rounding
using q+M-m<=binom(M,2) gives final-vertex lower bounds153,33639,1885253341
for (d,m)=(16,33),(32,65),(64,129). These are not claimed optimal sizes or
actual constructed completions. The enormous numbers come from the all-k
proof, not execution or enumeration of billions of subdivisions.

### Positive direct original routes on the SAME family

Classical cyclic-facet domino structure gives an explicit direct route of at
most2k^2 edges for arbitrary endpoints of P_k. This is weaker than Maksimenko's
known exact cyclic diameter formula, which gives2k here; the primary abstract
was read and cited. No new best cyclic-polytope result is claimed.

For disjoint active endpoints {1,...,2k} and {2k+1,...,4k}, packed-block shifts
take exactly2k edges. Each original edge can leave at most one source facet,
so these selected routes are shortest. The completed d16/32/64 runs audit all
17/33/65 vertices and16/32/64 original edges by exact root-polynomial supports,
rank and adjacency identities. No large full vertex graph or complete flag
refinement is constructed. Arbitrary endpoint routes are not asserted to keep
all common facets; the selected large controls share none.

Thus d64/m129 has a certified shortest64-edge route while any full forward-
stellar flagification needs at least1,885,253,341 vertices. The obstacle is the
GLOBAL M-d size account, not the existence of a short original route or even
a short path inside an implicit huge refinement.

### What was actually checked and delivered

515 literal stellar subdivisions on all114 four-label complexes, including77
larger-face moves;1204 old-descendant checks;160 randomized sequences with948
steps;7296 old graphical cases,6766 valid flag refinements. Four simplex
completions and eight saved ancestry packets replay exactly. Abstract test
complexes are not all polytopal; only the general combinatorial claims are
applied to them.

The small moment families have285 individually checked nonface certificates,
348 proper-face witnesses and60 genuine-row exposures. Larger d16/32/64 cases
have nine additional nonface and nine proper-face samples TOTAL; the entire
exponential subfamily is covered by the written proof, not a claimed enumeration.

Independent complete small original graphs test all126/1716 active sets and
produce27/156 vertices,54/468 edges. Across351 exhaustive plus120 sampled
endpoint pairs, the direct router uses1576 edges vs1369 BFS, with110 nonshortest
routes. It is a control, not a better default. Fourteen malformed/out-of-scope
controls fail; five route consumers replay with route production disabled.
Integer lower bounds are checked through k80 in addition to the all-size proof.

All seven uploaded blobs match local bytes. The full suite reproduces in a
clean workspace with TWO new scripts and FIVE byte-identical dependencies.
Every report field except seconds and the244669-byte fixture agree exactly.
A separate seven-addition patch applies in a fresh dependency-only Git checkout,
passes Python compilation and reruns the whole suite with matching results and
fixture. These are not full repository/Lean builds. Python and JSON parsing are
not Lean-extracted. No Actions or Prove2Me gate was requested.

    python3 scripts/test_stellar_nonface_persistence.py
    python3 scripts/stellar_nonface_persistence.py --k 32

## Earlier positive class results remain valid

Accepted allocation/representation results through #236/#237/#241 and the
Minkowski edge/fibre chain #239--#245 are not an uncompiled backlog. #244 owns
its remaining assembly. #246/#247 image-edge/minimal-face certificates, #248
valid-edge selection and #250 face locking retain their own exact hypotheses.
Count ORIGINAL IMAGE facets; arbitrary extension edges can become chords.

#253--#259 provide original-edge selectors, low-dimensional weighted bounds,
explicit barriers, and the exceptional-label route count. Their limitations
and exact receipts remain in the prior frontier. A bound on all available
vertices differs from a bound on what an actual route visits.

#260 block refinement, #261 repeated-incidence compression, #262 exact birth/
death accounting and #263 polytopal plateau macros remain correct under their
stated conditions. #264's additional energy/plateau branch is separately owned.
The new obstruction is broader than failure of any one of their planners;
class-specific small refinements are not contradicted.

#265 gives COMPLETE cactus-incidence schedules with
 t<=W+long_cycles<=supported_labels-2*components,
and the inherited original bound2m-d-2c. It handles many cycles sharing label
or defect articulation nodes. Non-cycle biconnected blocks remain outside its
hypothesis. Its all-dimensional wedge/cactus examples and adverse comparisons
are preserved in research/CACTUS_FLAG_REFINEMENT.md and sidecars.

#266 gives a graphical nested refinement flag exactly when each original minimal
nonface has at most two induced graph components. Its full size M counts ALL
connected original faces. Paths/degree-two graphs have polynomial inventories
when that criterion holds; existence is not universal. Those files are unchanged.
The new lower bound extends the obstruction beyond degree two to ANY auxiliary
graph whose resulting complete flagification is such a forward stellar sequence.
It still does not force a long selected path or contradict its special classes.

## Next research: use a path-local quantity or a different construction

Do not use 'find a polynomial-size complete forward flagification for every
polytope' as a new open child or an optimistic unproved premise. A replacement
could attempt to bound only the refined labels/edges actually used by a route,
avoid completing unrelated portions of an implicit refinement, or construct
original edges directly. The cyclic controls now test whether a proposal can
avoid globally resolving exponentially many irrelevant incompatibilities.
No such universal path-local bound is proved here.

Inverse moves/coarsenings are outside the persistence invariant, but would need
a new original-edge transport argument; do not assume the forward carrier proof
works backward. Arbitrary flag subdivisions without a forward factorization
are also not ruled out by this result. Keep those distinctions explicit rather
than interpreting a strategy obstruction as evidence against Polynomial Hirsch.

#244 assembly, #238 support witnesses, #250 projected integration, #255 shortening
and #264 energy work are unchanged. #208 needs its approved existing poll, not
duplicate submission; #210 stays retired/reserved. Recheck live ownership.
Written mathematics, exact tests, Lean compilation, axiom audit, ACCEPTED and
authenticated Proved are distinct statuses. Preserve toolchain pins, credentials
and trusted-publisher isolation; research-only work needs no speculative gate.
