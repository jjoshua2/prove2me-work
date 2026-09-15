# Current Polynomial Hirsch frontier

Repository `jjoshua2/prove2me-work`. Keep Lean `v4.30.0` and Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`. Read AGENTS.md, CLOUD_AGENT.md,
SKILL.md, CONTINUE_HIRSCH.md and the LIVE PR heads/comments before choosing work.
Do not resubmit accepted/pending packets or infer the frontier solely from an
older status overview. The exact main commit may contain newer merged work.

The immediately preceding COMPLETE status is preserved in immutable Git history:
[pre-weighted-retirement STATUS](https://github.com/jjoshua2/prove2me-work/blob/9c86ff0dc37741eae516e29ea95a441583cf29c3/STATUS.md),
Git blob `e40642e7d620e108b4257938c1959492d87f51af`. It contains the complete
#252 record and links to every older accepted-result archive. This index adds
#253/#254 research; it upgrades no numerical result to a Lean/platform verdict.

## Conjecture-level objective and accepted interfaces

The last preserved authenticated mission audit reports root
`58eae2c9-6fd5-4d5d-8aa7-6d552ad80bac` Open and remaining high-dimensional leaf
`Hirsch.common_face_diameter_of_dim_ge_six`,
`87a8b4f4-8b58-4340-8cb9-5fd1b548d01e`, Open. This is NOT a fresh platform poll.
The target remains a uniform polynomial number of genuine ORIGINAL ordinary
edges for arbitrary high-dimensional carriers. Original image facets, not a
smaller extension's rows, are the relevant size. Projection may turn source
edges into interior chords.

The checked-allocation chain through #236 and coefficient/image results #237/#241
are ACCEPTED and complete; do not restart old blocked or uncompiled bundles.
The genuine Minkowski edge/fibre chain #239--#245 is preserved in the previous
archives. #244 retains its separate core-walk concatenation. Its supplied-model
L+(L+1)K estimate is not controlled decomposition existence for every carrier.
#246/#247 give original-row image-edge certificates and minimal-face discovery.
Accepted #248 gives genuine normalized-tangent image-edge selection, not a
polynomial route-length or simplex-pivot bound.

#250's face-locking theorem has an ACCEPTED bot verdict: theorem
d67aa510-011e-4a33-bbc3-87ba15d20e15, submission
5de1a327-e11c-4959-be0a-12ac37e55169, run34905478804 at proof
c4a3de644ffa6dceaa6a68ea05b7e458078feb67. Its owner retains general projected-
image implementation/integration. Read its own latest receipts and live state;
this update does not constitute another authenticated platform query.

## Completed research #252: acquisition can justify objective decreases

[Proof and tests](research/TARGET_PHASE_ACQUISITION.md),
[handoff](research/TARGET_PHASE_HANDOFF.md). Merged26912292ae3b64956d63137042cfdf95ab11df13.
This is research/code, not a new Lean or Prove2Me theorem. The simple original-H
selector locks target facets, fixes a reciprocal-target-slack objective within
each phase, and prefers one/two-edge acquisitions even if the old objective
decreases. Otherwise it takes a completed positive-gain edge. Finite termination
and affine/positive-row-scale invariance are written and tested.

Fixed-radius lookahead does NOT bound phase length: explicit parabolic polygons
force N+1 selected edges versus h+2 shortest when the useful exit lies beyond
horizon h. At depth2,N64 the actual comparison is65 versus4 on69 original
facets. This is linear in facets, not a Hirsch counterexample. Full #252 counts,
nonshortest cases, nine regressions versus the earlier target-slack baseline,
and precise implementation limits are preserved in its note and prior STATUS.

## Completed research #253: complete two-faces and permanent subset charges

Merged `9456445941adbbfd6464d8bd1d559599d6f3ea18`, source head
`beb65c4f5e43383590fe0d8b95cff8d42014cfa1`.
[Mathematical proof](research/TWO_FACE_ACQUISITION.md),
[handoff](research/TWO_FACE_HANDOFF.md),
[execution summary](research/TWO_FACE_ACQUISITION_SUMMARY.json).
The actual selector is scripts/two_face_acquisition.py, Git blob
aa562f02dd492ecc47479381d637c6292757ebd3. Do not duplicate it as a new polygon
search merely because the previous index still named only #252.

For a simple bounded original d-polytope with m facets and e=m-d, every two-face
has at most e+2 sides. At retained dimension h there are binom(h,2) incident
polygons. Trace all of them completely, retaining locked target equalities.
Choose a shortest first target-acquisition arc when one exists; it has at most
floor((e+2)/2) original edges. Otherwise take a strictly increasing boundary
arc to an endpoint dominating the maxima of ALL inspected faces, not merely
a single local pivot. This stronger fallback is essential to its accounting.

Every fallback retires at least h-1 improving original two-face labels. None
can receive another charge in the phase; after acquisition they are disjoint
from the new retained face. Thus

    (h-1) B_h <= binom(e,h-2),
    L <= r floor((e+2)/2) + sum_{j=2}^{r-1} binom(e+1,j).

This is a derived count for the actual selector, but the binomial sum is still
exponential in unrestricted r,e. It is not Polynomial Hirsch or a newly best
classical general diameter estimate. The rule is shortest on affine products
of polygons without a supplied factor chart; a truncated-octahedron example
shows that a fallback can really be necessary. Per-decision work and committed
route length are separate. Prior exact comparisons, regressions, and complete
cycle/edge-label audits are in #253's own records; no #253 tests are relabeled
as a new execution merely because they are cited here.

## NEW merged research #254: linear weighted three-face tail

Research head `7570ffd05b2ab913417094f41f28e142f519cf49`; merge
`9c86ff0dc37741eae516e29ea95a441583cf29c3`.
[Complete proof](research/WEIGHTED_FACE_RETIREMENT.md),
[executed report](research/WEIGHTED_FACE_RETIREMENT_TESTS.json),
[handoff](research/WEIGHTED_FACE_RETIREMENT_HANDOFF.md), and source manifest.
Six additions only. The independently prepared duplicate polygon selector was
WITHHELD after reconciling #253; all reported new tests use the EXACT unchanged
#253 code and unchanged original-row auditor. No existing source is modified.
No Lean declaration, compiler/axiom gate or Prove2Me submission was created.

The new account charges each distinct CHOSEN fallback polygon its actual q-1
edge cost. If the retained target face has dimension3, the polygons are facets
of a simple three-polytope and are disjoint from its three target facets. Their
dual vertices have every neighbor in the induced non-target planar graph on
at most e vertices. The sum of available degrees is at most6e-12. Hence

    L_fallback <= sum_selected(q-1) <= 6e-12-B,
    L <= 6e-12 + 2 floor((e+2)/2),      r=3.

The remaining polygon tail after the first acquisition is shortest. For r=2,
L<=floor((e+2)/2), and for r<=1,L<=r. These are unconditional bounds for this
selector in the stated simple/bounded class, not a newly assumed short-phase
premise. They apply to intrinsic three-faces in high ambient dimension. The
new ledger verifies an existing route; it does not change path selection.
Stronger classical three-dimensional diameter results already exist: this is
an algorithm-specific accounting improvement, not a new best classical bound.

For initial r>=3 the global account becomes

    L <= (r-1)a+6e-12+sum_{j=3}^{r-1} binom(e+1,j),
    a=floor((e+2)/2),

or the minimum with the older bound where useful. The last sum STILL prevents
a uniform polynomial conclusion. Planarity controls the final three-face tail,
not arbitrary higher-dimensional retired-face incidence.

### Sharp-order corridor and actual unchanged-code checks

For every m>=8, exact rational stacking/polarity constructs a simple original
three-polytope with m genuine facets,2m-4 vertices, and every polygon size<=6.
Source and target share no facet. All primal triangle labels have span<=3;
even a WHOLE incident-polygon macro can advance the largest active label by
at most3. A target acquisition is impossible until it reaches m-6, starting2.
Thus first-phase fallback macros obey

    B_3 >= max(0,ceil((m-8)/3)).

Together with #253's upper bound this gives Theta(m), despite fixed dimension,
small polygon faces and at most three acquisitions. It is a linear lower bound,
not a Hirsch counterexample or a superpolynomial shortest-path obstruction.

Actual #253 for m8/12/16/24/32: fallback macros0/2/4/7/10; route edges
4/7/11/17/23; independent reference distances4/7/9/15/20. Nonshortest cases
remain. At m32 the generic certified count drops480 to192, not the actual23-edge
path. All larger reference graphs come from checked complete stacking transcripts;
only m8/m12 also have a separate exhaustive active-subset enumeration.

Four independent small original graphs give808 ordered pairs and2036 edges.
Every weighted charge and dual incidence is checked against those reference
graphs, never supplied to the selector. Eight nonshortest pairs remain. There
are23 corridor macro-span checks; three intrinsic-three-face embeddings in
ambient dimensions4/8/16; nine search-disabled audits; seven rejected forged
or unsupported certificates. Rational sizes are recorded, with no small-bit
claim. The full suite reproduces in a clean two-dependency workspace; all result
fields except time and the complete generated fixture agree byte-for-byte.
The six-file patch separately applies and reproduces every addition exactly.
These are numerical checks and written mathematics, NOT Lean-extracted code.

    python3 scripts/test_weighted_face_retirement.py

## Next quantitative work and ownership

The next conjecture-facing target is a polynomial WEIGHTED account for the
SELECTED high-dimensional retired-face family, or a different global original-
edge invariant. Counting all non-target facet subsets leaves an exponential
supply; using a largest-face cost repeatedly can further overcount it. #254
shows how actual incidence removes that latter loss in a three-face, and its
corridor shows why constant fallback counts cannot replace an n-dependent proof.
Do not reimplement complete two-face acquisition or claim that planarity extends
to arbitrary dimension. Low-dimensional/fixed-deficit existence results in the
older verified carrier framework remain available and are not republished here.

#244 retains core/fibre assembly; #238 support-witness existence; #250 general
projected-face locking. No other agent's branch or active submission was modified
or retriggered by #254. #208 remains a distinct recorded pending submission until
properly polled; do not resubmit from stale status. #210 is retired ancestry.
Read the live queue and exact heads before selecting a newly overlapping task.

Use local pinned Lean for formal iteration where available. Written arguments,
exact Python, compilation, axiom audit, ACCEPTED and authenticated Proved are
different statuses. Research-only work does not need a speculative hosted proof
gate. Keep secrets in the trusted main publisher; no workflow, pin or permission
changes. Preserve exact raw evidence and label derived summaries honestly.
