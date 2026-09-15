# Current Polynomial Hirsch frontier

Repository `jjoshua2/prove2me-work`; refreshed September 15, 2026 UTC.
Keep Lean `v4.30.0` and Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
Read AGENTS.md, CLOUD_AGENT.md, SKILL.md, CONTINUE_HIRSCH.md and the LIVE PR
heads/comments before choosing work. Do not resubmit accepted/pending packets.

The immediately preceding COMPLETE frontier is retained verbatim in Git history:
[pre-confinement STATUS](https://github.com/jjoshua2/prove2me-work/blob/66049587d5902fd7fa4816325ca94a975b914727/STATUS.md),
blob `32dd42acc614c7b3a75da79681f38116bb978025`. It preserves every older
accepted-result archive, #257/#258 formula and limitation, test count and ownership.
This update adds research/software; it upgrades no written proof to a Lean or
Prove2Me acceptance.

## Conjecture-level objective and unchanged accepted work

The last preserved authenticated mission audit records root
`58eae2c9-6fd5-4d5d-8aa7-6d552ad80bac` Open and remaining leaf
`Hirsch.common_face_diameter_of_dim_ge_six`,
`87a8b4f4-8b58-4340-8cb9-5fd1b548d01e`, Open. This is NOT a fresh platform poll.
The target is a uniform polynomial number of actual original ordinary edges
for arbitrary high-dimensional carriers. Use ORIGINAL IMAGE facet counts:
short auxiliary paths can project to chords.

The checked-allocation/representation chain through #236/#237/#241 is accepted,
not an uncompiled backlog. The genuine Minkowski chain #239--#245 remains in
the archives; #244 retains independent core-walk assembly. Its supplied-model
L+(L+1)K does not produce a controlled useful decomposition for every carrier.
#246/#247 provide original-row image-edge/minimal-face certificates. #248 selects
valid normalized-tangent edges without a route-length bound. #250's preserved
face-locking acceptance and general projected-image integration remain its
owner's work. Read their exact current receipts before using or modifying them.

## Research frontier inherited from #252--#258

#252 allows target acquisitions with objective decreases; bounded lookahead has
explicit long-phase controls. #253 traces COMPLETE incident polygons and takes
fallbacks to their common best maximum; its retirement theorem does not apply
to a weaker one-pivot fallback. #254 weights selected polygon costs and proves
a linear intrinsic-three-face tail, with a matching-order stacked-polar corridor.
#255's same-anchor shortening/hidden-target family and #256's projective slack
barriers remain distinct work.

#257 counts pre-acquisition vertices after target deletion using an analysis-only
cap and classical UBT. Its refined Fibonacci bound remains exponential; its
hidden-target example has an actually exponential relaxed inventory. The original
algorithm does not route in the relaxed polyhedron. A universal polynomial bound
on that entire inventory would be false.

#258 implements classical Adiprasito--Benedetti segments directly from original
rational H queries. Its source remains unchanged. Original feasible or strict
nonnegative-dual certificates establish every link intersection; original inverse
identities/maximal ratios establish each edge. The consumer replays BFS/recursion
but performs no geometric discovery/LP/inversion. Its exact raw ledger is

    L = distinct_original_facets_seen - d + facet_reentries.

The classical flag guarantee sets the last term to zero, but arbitrary inputs
are not assumed flag. Labbe--Manneville--Santos arXiv1510.07678 proves examples
where EVERY raw combinatorial segment is exponentially long, even though short
routes exist. Tie changes within that family are not a universal fix. #258's
strictly shorter in-facet splices may leave that restricted route family; their
universal success or polynomial cost is not proved. The old full test counts,
mixed performance and local missing-triangle witnesses are in the prior index.
Do not repeat the flag theorem or claim the new component dominates #253.

## NEW merged research #259: confined exceptional facets

Research head `14b6d5f41b1d20f38368d4fd245e432321afdd34`;
merge `69d1865846f09a7f85426b8534cadde7785f3d2a`.
[Full argument](research/DEFECT_CONFINEMENT.md),
[exact test report](research/DEFECT_CONFINEMENT_TESTS.json),
[handoff](research/DEFECT_CONFINEMENT_HANDOFF.md), source manifest and clean replay
are on main. EIGHT additions; no older selector, proof, pin or workflow changed.
No Lean declaration, compiler/axiom gate or Prove2Me submission was created.

### Actual structural hypothesis, not a short-route premise

For a simple bounded full-dimensional original d-polytope with m genuine facets,
choose B containing k exceptional facet labels, g=m-k protected labels, e=m-d.
A global sufficient condition is that EVERY inclusion-minimal empty facet
intersection of cardinality>=3 is WHOLLY CONTAINED in B. Alternatively certify
that every missing triangle in every recursive link actually visited by the
specified #258 segment has ALL THREE labels in B. Intersections include the
locked original rows of each link.

Merely hitting each missing face with one label is NOT enough. Deleting B to
leave a flag induced subcomplex is not the stated condition. Bounding sizes of
individual missing faces does not bound their union. These distinctions have
explicit negative tests, not just prose warnings.

The protected-label specialization of the AB induction implies each facet
outside B is nonrevisiting. The only relevant flagness use fills triangles
containing that protected label and consecutive necklace anchors, recursively
in actually used links. The global condition implies local confinement because
any minimal nonface inside a missing link triangle plus locked rows must include
all three triangle labels. The proof and scope are written explicitly in the note.

### New finite-state count, including actual exceptional reentries

Erase complete-vertex loops. For a fixed active exceptional subset S, every
later distinct vertex with that same S must introduce a new protected label.
Otherwise protected-label interval membership forces the same complete active
set. Thus at most g-d+|S|+1 vertices have that signature, giving

    L <= sum_{s=max(0,d-g)}^{min(k,d)} binom(k,s)*(g-d+s+1)-1
      <= (e+1)*2^k-1.

For k<=min(d,e), k>=1, the sum is2^(k-1)*(2e-k+2)-1; for k0 it is e. This is
LINEAR in facet excess for fixed k, polynomial if k=O(log m). No theorem says
that regime holds for arbitrary carriers. This is a bound on the delivered
loop-erased route, not on the work of producing/erasing a longer raw segment,
LP pivots, or recognizing a small global core.

A certified empty ORIGINAL subset inside B excludes its active signatures and
sharpens the sum. The checker uses only original separated_rows dual identities;
an empty link S+T is never misreported as globally empty T. Enumeration of the
optional signature refinement is capped at16 labels. An arbitrary later repair
must recheck protected intervals rather than assume they survive.

### All-dimensional nonproduct class with a linear bound

For d>=3, let S=x0+x1+x2 and define

    0<=x_i<=1,
    S<=5/2,
    S-x_j<=5/2-2^(-(j+1)) for j>=3.

There are3d-2 genuine facets and one high minimal nonface, the first-three upper
coordinate facets. Successive shallow protected-ridge truncations preserve
this triple by the proved stellar-subdivision lemma; every other minimal
nonface is a pair. The minimal-nonface hypergraph is connected, excluding a
nontrivial COMBINATORIAL Cartesian product. Minkowski indecomposability is not
claimed. The construction proves simplicity/irredundancy in all dimensions.

Excluding the impossible active triple improves the class bound to

    L <= 7e-6 = 14d-20    for EVERY endpoint pair.

Its vertex count is(3d+11)*2^(d-4) for d>=4, and10 for d3. At d12 it has34
original facets and12032 vertices but the all-pairs bound148. The sampled path
has12 edges; do not confuse that with a universal shortestness claim. This is
not a new best general diameter bound or an unrestricted solution. The small
exceptional parameter differs from the classical banner threshold: critical
nonface cliques of size d+1 remain in this family despite k3.

### What was executed and what was not

The full suite checks83 geometric routes and28568 used-link triangles. Family
d3/d4/d5 has63 endpoint pairs,162 original edges and1532 independent square
systems, with complete clipping/minimal-nonface/reference agreement and strict
facet anchors. Fourteen named historical INPUTS are regenerated afresh rather
than replayed as old verdicts. Three further holdouts have REAL exceptional-
facet reentries: two products in dimensions4/6 and one nonproduct4D cross-cut
with the same six-label core. The new count permits these reentries; it does
not falsely report them removed. Larger local exceptional sets are retained.

Family d6/d8/d12 runs give6/8/12 selected edges and structural bounds64/92/148,
without enumerating full large vertex graphs. d6/d8 use generic exact LP. d12
uses an untrusted family-specific scalar/dual witness producer for the SAME
unchanged recursive selector; every answer gets the original-row audit. It is
NOT a completed generic LP replay. Generic/special full paths match in d3/4/5.

Standalone finite-state tests cover1638 random interval paths and9466 exhaustive
small paths. Seven malformed/unsupported controls fail;23 full certificate
replays pass with LP/inverse/basis/intersection production disabled. BFS and
recursion are still replayed. Python and JSON parsing are not Lean-extracted.

The full run repeats in a clean directory with only TWO new scripts, the small
input fixture and THREE unchanged dependencies. Every report field except
nested seconds and the17,809,933-byte full certificate fixture match exactly.
The eight-addition patch separately applies in a fresh dependency-only Git
checkout, matches all new bytes and passes Python compilation. The repository
stores report/replay hashes and a reproducer; the downloadable bundle includes
full detailed certificates. No numerical check is labeled Lean verification.

    python3 scripts/test_defect_confinement.py --large
    python3 scripts/defect_confinement.py input.json segment.json --output confined.json

## Remaining conjecture-facing task and ownership

The payoff for controlled exceptional states is now derived, not an assumed
short-phase lemma. The missing unrestricted step is to control the actual local
exceptional signature supply or reduce it with bounded original-edge cost.
Do not insert k=O(log m), polynomially many signatures or cheap repairs as
unproved hypotheses while claiming Polynomial Hirsch. Large k itself is not a
diameter obstruction: a simplex's unique high minimal nonface contains every
facet label although its graph diameter is1. Structural special classes are
useful but do not discharge arbitrary high-dimensional carriers.

#244 retains core/fibre assembly; #238 support-witness existence; #250 general
projected-image work; #255 same-anchor research is separate. None was modified
or retriggered. #208's recorded pending submission needs its own approved poll,
not a duplicate; #210 remains retired ancestry. Recheck live queues before
choosing a newly overlapping task.

Written proofs, exact software tests, Lean compilation, axiom audit, ACCEPTED
and authenticated Proved are distinct states. Research-only work needs no
speculative hosted gate. Preserve pins and the trusted-publisher secret split;
keep raw platform evidence separate from derived local summaries.
