# PR #312: original zonotope-edge criterion — ACCEPTED

Read current STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and live PR
heads/comments before continuing. This turn resumed existing #312 from main
7ed199c915cd97afd65008f7ba60e171e28a39cb. No duplicate target or PR was created.
Other owned work, accepted packets and reserved #210 were untouched.

## Authoritative accepted packet — do not resubmit

`Hirsch.zonotope_exposed_edge_iff_tied_collinear` is ACCEPTED, with authenticated
publisher readback Proved. Theorem bb32ac53-d8ba-4e21-92eb-b7e5ec568c70;
submission f68818e2-63ce-40b3-a104-e63e9b71b454.
Frozen proof fefbdd9f422a7f1511713b4e2e80934087d40389; run 35449401954.
Actual NEW top-level request 5742734506, exact-SHA acknowledgement 5742735713,
and verdict 5742760113 were read back. Gate/verify/publish completed successfully;
report-verify skipped. All three compile modes exit zero; all five transitive
reports contain only propext, Classical.choice and Quot.sound.

Read the packet's accepted-evidence.md, raw publication-receipt.json,
packet-audit.json, manifest and complete compiler logs, plus the labelled
verification/zonotope-wall/resume-publication-readback.json. Proved is the trusted
publisher's authenticated readback, not a separate direct platform or mission-root
poll. Missing individual API bodies are not invented.

## The existing repair is closed, not still pending

Accepted source: 454 lines / 18186 bytes; Git blob
fdae9555c66329742f641c259e551f03edad132d, SHA256
cdf116eed7169dd2e8ea0cd53c58154393689e8c052c4fa6301c1682ddd9aad5.
It is exactly the previously saved proposal. Only scalar_bounds' pair-proof
layout and line_face's mass nonnegativity lambda reduction changed. All
definitions, statements, assumptions, public root AND proof and both metadata
files remained unchanged. No further proof edits or triggers followed success.

First run 35448186683 remains a driver-compilation failure. Its source, request,
scoped diagnostic block and failed-elaboration reports are retained. The old
handoff is copied verbatim to handoff-before-acceptance.md. Old proposal metadata
saying uncompiled is historical: the exact proposal is now applied and accepted.
This was the SECOND compiler gate and FIRST actual platform submission, with
ONE new trigger this turn. Local Lean/Lake and compiler-host DNS were unavailable;
formal evidence is the pinned hosted gate, separate from rational/source checks.

## Exact original-edge interface now proved

For arbitrary finite real generators w_i and arbitrary linear f, let
Z=sum_i[0,w_i] and F={x in Z: f(x)=sum_i max(0,f(w_i))}. The whole face F is a
nondegenerate original exposed/extreme segment with extreme endpoints IFF all
objective-tied generators lie on one line and at least one is nonzero.
Collinearity is a necessary-and-sufficient condition, not a hidden genericity
hypothesis or a claim that all cube edges project to original edges.

Saturation fixes every non-tied coefficient in EVERY maximizing representation.
For collinear ties w_i=c_i*w_j, lower/upper endpoint choices yield displacement
(sum_tied |c_i|)*w_j with positive width. Scalar bounds put the entire face in
that segment; interpolated coefficients give the converse inclusion. Tied
corner toggles prove necessity and the existence of a nonzero direction.
Original exposed-face extremality gives actual vertex endpoints.

Repeated, opposite, zero and rank-deficient generators, zero objective, m=0 and
d=0 are included. No vertex catalogue, edge oracle, rank witness or short route
is supplied. This full iff and its constructive half are CLOSED. Reuse the
accepted code rather than another child assuming the same missing whole-face
result. The two elementary segment helpers retain the accepted #309 proof bodies.

## Remaining route and conjecture boundary

A next objective-sweep route proof must construct suitable objectives for the
requested actual endpoints, avoid simultaneous independent-direction ties, allow
parallel repeated ties, and count genuine transitions. This packet does not
construct that sweep or prove any all-pairs length bound. A use on #311's
translated pair completion also needs explicit transport; coefficient-cube
adjacency is not a substitute for this original-face criterion.

The accepted #309 contraction, #310 endpoint lifts and #311 whole-set completion
remain available, without resubmission. Their generator inventory still is not
a polynomial bound in original H facets. Neither a general facet-polynomial
completion budget nor unrestricted Polynomial Hirsch is established here.
Classical face geometry is credited; no historical-priority claim.

## Reproducible evidence

Four original ZIP hashes and all five frozen packet hashes were recomputed.
Raw extracted compiler/manifest/audit/request/receipt files are preserved separately
from derived run/check summaries. The verify and publish logs were inspected
through cleanup; complete runner-log files are not falsely claimed committed.
The export contains all four original ZIPs and complete test outputs.

The unchanged Fraction suite ran again and in a clean script-only workspace:
66 small systems, 987 objectives, 37894 saturation checks, 2961 fractional cases,
236 edge faces, 751 nonedges and all 75 independent original planar edges.
Five selected models reach d64 without full graphs; 27 saved certificates audit
with discovery disabled, and five forgeries are rejected. The projected cube-edge
hexagon countercontrol remains retained.

Report 27430 bytes, SHA256
42ad193e6b3436487beed34b380ac5e5257af2c68dc8a044e9856bf8615c1386;
fixture 36496 bytes, SHA256
8ddda93ad1deeb89da2d00ca7c773c2c1977f03090d26ec6283efb5e5693118b.
Both reproduce prior bytes exactly. These are not additional Lean theorems or
verified Python/JSON. Reproduce with:

    python3 scripts/test_zonotope_wall.py --out /tmp/zonotope-wall

Lean 4.30.0 / Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f, strict 0.10.5
guard, workflows, actor allowlist, duplicate safeguards and credential isolation
are unchanged. Consult current PR metadata for the later evidence/merge SHA.
