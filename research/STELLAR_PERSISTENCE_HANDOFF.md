# Continue beyond full forward-stellar flagification

Read LIVE STATUS/main and PR ownership. Base for this contribution:
8f7ae8d325e38b5fce9753a8b7efb995b8a9af5b. #265 cactus research and #266 graphical
research are retained unchanged, and #264's active work is not modified.
This packet is written research/exact Python, NOT Lean or Prove2Me verification.

## Main consequence: a universal polynomial full-refinement premise is false

For ANY true face E with |E|>=2, an old minimal nonface N has a minimal descendant
N if E is not contained in it, otherwise (N minus E)+{z}. Distinct N have distinct
descendants. The old face E is one additional new minimal nonface. This is proved
by checking all single-label deletions using the actual stellar face definition.
It is not a hypothesis of the planner and does not concern just higher defects.
After t forward steps, q original minimal nonfaces plus t mandatory born roots
remain distinct. Flag completion on M=m+t vertices therefore requires

    q+t <= binom(M,2).

A certified SUBFAMILY of original minimal nonfaces is enough for this lower bound.
No full exponential original catalogue need be enumerated. The initial roots
also preserve the union of their original carriers throughout the sequence.
The old W may decrease by converting high defects to pairs; that does not remove
these roots. Larger-face moves, neutral steps, energy-increasing steps, unbounded
macro horizons and different forward schedules all remain subject to this count.

Rational family: P_k is the polar of the mean-centered moment points
(t,t^2,...,t^(2k)), t=0,...,4k. It is simple, dimension2k, with4k+1 genuine facets.
Every (k+1)-subset of odd labels {1,3,...,4k-1} is a minimal nonface. Proper faces
have squared-root support polynomials; the whole subset has an alternating
positive affine-circuit obstruction on interleaved even separators. Thus
q>=binom(2k,k+1)>=4^k/(2(2k+1)) and every final flag M>=2^k/sqrt(2k+1).

Exact lower bounds: d16/m33 requiresM>=153; d32/m65 requiresM>=33639;
d64/m129 requiresM>=1885253341. These are NOT optimum constructions or original
diameter lower bounds. They rule out universal polynomial TOTAL SIZE for the
full forward stellar approach before applying the classical global M-d bound.
The graphical and block nested refinements also have forward stellar sequences,
so dense graphs and new schedules alone do not repair this worst case.

Do NOT overgeneralize to arbitrary subdivisions without a forward factorization,
inverse stellar moves/coarsenings, or all routes inside a huge refinement.
Those are outside the invariant. Existing class-specific positive theorems are
unchanged. No conjecture counterexample or general route impossibility is claimed.

## Positive original-edge control on the SAME family

Classical cyclic-facet runs can be paired as dominoes after cutting at a common
absent label. Packed-block shifts toward target positions make one original
facet exchange per step and decrease total start-coordinate distance. This gives
an elementary all-pairs route bound2k^2, not a new best classical diameter bound.
Selected endpoints {1,...,2k} and {2k+1,...,4k} take2k moves. They share no original
facet, so the source-facet-drop lower bound proves these selected paths shortest.
The complete d16/32/64 routes are actually executed and all17/33/65 vertices
checked by original-H root-polynomial certificates. No large full graph is
constructed. General direct routes are NOT asserted common-face-preserving.

Maksimenko2009 DOI10.4213/dm1054 already proves the exact diameter is2k for these
parameters; the primary abstract was read. Our quadratic construction is weaker,
and small tests retain110 nonshortest cases out of471 tested pairs. It is a
control/explicit alternative, not a universally better default or a new cyclic
polytope theorem. Some finite negative results in older research concern different
route families; this full-size obstruction must not be conflated with them.

## What ran

515 literal stellar subdivisions on all114 four-label complexes, including77
non-edge faces,1204 old-descendant checks;160 random sequences with948 total
steps;7296 old graphical complex/graph cases,6766 valid flags. Eight ancestry
packets replay. Small moment tests explicitly certify285 distinct minimal
nonfaces,348 proper faces and60 genuine original facet rows. Large samples
certify nine more nonfaces and nine proper faces, not the full catalogues.

Two independent small graphs inspect all126/1716 active sets, yielding27/156
vertices and54/468 edges. There are351 exhaustive and120 sampled pairs,1576
new edges versus1369 shortest,110 nonshortest. Three large direct routes use
16/32/64 original edges, independently shortest for their supplied endpoints.
Fourteen malformed/out-of-scope controls fail. Route consumers replay with route
production disabled. Integer bounds through k80 are exact supplemental checks,
not the all-size proof. The proof and report explain every scope distinction.

    python3 scripts/test_stellar_nonface_persistence.py
    python3 scripts/stellar_nonface_persistence.py --k 32

The two new scripts depend on five byte-identical earlier scripts. The raw
report, full worked fixture and logs are bundled. Clean replay/source manifests
are local checks, not platform receipts. Python and JSON are not Lean-extracted.
No Lean/Actions/Prove2Me gate should be triggered for research-only code.

## Next actual task

Do not reopen 'find a polynomial-size full forward flag refinement for every
polytope' as if it were merely an unproved useful premise. A possible replacement
is a path-local bound in an implicit refinement or a genuinely different direct
original-edge construction. An inverse/coarsening operation would need its OWN
transport proof; the forward carrier lemma cannot simply be assumed backward.
The controlled d64/129-facet instance now tests whether a candidate algorithm
avoids refining the exponentially many irrelevant incompatibilities. No such
unrestricted algorithm or polynomial visited-state theorem is supplied here.
