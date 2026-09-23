# First gate: extreme tilts clean; two comparison annotations parse incorrectly

PR #338 is OPEN/DRAFT, not accepted or merged.
Target: Hirsch.strict_convex_chain_exact_source_rank.
Tested proof e7e191e7d8557d54f2cd296d43308b2d80ff794b on main
6ee1612a05cede29039c4728825b7d5d255f14a8. Source351 lines/15116 bytes,
blobf38406afe0468a91aac1efd1b7a847e67db05176, SHA256
153682c72d5f9627f7155bb712e61db22fbaa11a2e9cd7d9502bd1c7dc4e7e02.
No tested source or metadata changed after the gate.

## Actual result and narrow repair

Actual top-level request5798271256 and acknowledgement5798274474 resolve
run35886406394 to the exact proof. Gate107267547134 succeeded; verifier107267624342
failed driver compilation. Standalone solution and exact target statement were
not reached. Publisher107268320514 and report-verify107268321204 were skipped.
No registration, proof submission, theorem/submission IDs, verified archive,
publication receipt, ACCEPTED or Proved was produced. One hosted attempt;
no second trigger. Local Lean/cache unavailable and toolchain-host DNS failed.

There are two root parse sites, lines104 and162, each spelling the intended
comparison as k<i. The actual diagnostic elaborates @PrincipalSeg k instead
of an order proposition. The nine displayed errors include downstream type and
unsolved-goal cascades. Preserve the whole diagnostic rather than describing
only the first parser error.

The named reports for tilt_chain, extreme_tilts and reciprocal_card contain
only propext, Classical.choice and Quot.sound. rank_lower_bound, exact_rank and
public solution retain failed-elaboration sorryAx. No admission was written;
the full theorem is NOT verified.

The proposed repair adds spaces in exactly those two annotations: k < i.
It changes no declaration signature, public hypothesis/type, metadata, or any
other proof text. Patch:
research/verification/convex-chain-source-rank/first-attempt/proposed-spacing-repair.patch.
UNAPPLIED to publication source and UNCOMPILED. Proposed source351 lines/15120
bytes, computed blob668d5a54143923d16c293393c6affb3ab2759d16, SHA256
dc2a830c3da548edd4d1949235fbb5c0eb4f4178e9a5665b5744b74fe5048afe.
Apply/check/reverse succeeds. Further errors can appear; source checks are not
compilation. Resume this same PR after checking live ownership and pending runs.

## Mathematical progress and exact remaining scope

For ordered real abscissas and strict triple-secant convexity, the complete
written proof derives minimum DISTINCT upper heights min(k,n-k) over every real
tilt. Strict convexity forces one entire side above the source, injectively;
a common finite secant bound derives two extreme tilts attaining all minima.
Positive translation and reciprocal order give exact rank min(k,n-k)+1 and
twice-rank<=n+2. The witnesses and bound are derived, not hypotheses. Strictness,
ordered abscissas and the fixed chain remain essential. Signed heights, endpoint
sources and chains of sizes1/2 remain included.

The explanation separately proves the planar polygon-to-chart construction from
actual vertex extremality and gives original supporting-edge/facet interpretation.
Those geometric bridges are WRITTEN and tested, not additional Lean output from
this finite-chain packet. No arbitrary-dimensional polynomial rank bound, new
historical planar-diameter theorem, numerator re-selection or implementation
extraction is claimed. The other agent's claim5786607495 remains untouched.

## Executed tests and preserved evidence

24 completed configurations produce2030 routes/11464 original-edge occurrences
through1840 checked state transitions,1084 of which acquire no target row.
The new closed-form algorithm completes the exact old64-vertex EIGHT-target
scope:512 routes/8192 edges, without arrangement enumeration. It does not change
the historical status of the previous algorithm's timeout. Small/random tests
compare9194 exhaustive sweep cells and directly check9188 strict triples. All
20130 pair-secant/weighted identities are checked; the large case contributes
15624 of these and does not exhaust triples. Ten malformed/premise controls fail.
All six full outputs repeat byte-for-byte in a clean four-script workspace.

Two new scripts and two unchanged #337 dependencies are used. No old blocked
solver is used or copied. Scripts, Python/JSON and the written polygon bridge
are not kernel-verified. Full fixtures are exported and regenerate; repository
summaries are labelled derived. The initial exploratory3934 states are separate
from completed regression totals; the harness tuple-mutation fix is recorded.

Only request artifact10762459258 exists:312 bytes, SHA256
c5f07f8d3fc0a163a879d003a083fa4346d1acb88c7a9aff5d329c6b8b97b689.
Its original ZIP and resolved.json were downloaded/rehashed. Complete displayed
diagnostics and all six reports are preserved with timestamps omitted; selected
runner lines are not a full raw runner archive. The full decoded job log was
read through cleanup. No missing artifact or platform response is invented.
Handoff: research/CONVEX_CHAIN_SOURCE_RANK_HANDOFF.md.
Keep Lean4.30.0/Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.8,
all publication safeguards and other-owned #326/#282/reserved #210 unchanged.
