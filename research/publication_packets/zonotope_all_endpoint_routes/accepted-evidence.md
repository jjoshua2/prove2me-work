# ACCEPTED: arbitrary-endpoint original zonotope routes

Theorem: `Hirsch.zonotope_all_endpoint_original_routes`.
Theorem ID: `26dac93f-73ea-405f-9597-11a05db6f697`.
Submission ID: `d9928e58-dff8-4a57-ae0f-cb4e15d2523d`.
Authenticated verdict: **ACCEPTED**. Publisher live readback: **Proved**.
Do not resubmit this packet.

## Actual comment, proof and verification

New top-level PR #316 conversation comment 5749637387 began
`/prove2me publish research/publication_packets/zonotope_all_endpoint_routes`.
It was read back. Acknowledgement 5749638345 resolved exact proof
13365da5ce10b03628d9db83c4896360893c74ef and run 35509181938.
Verdict 5749652320 was posted at 2026-09-20T11:59:00Z and read back.
Trusted workflow/publisher main was c9a9a44a0d144efa66c07c2c26605adafd0c2dd3.

Gate 106073991194, verify 106074012796 and publish 106074147720 completed
successfully; report-verify 106074148384 was skipped. Driver, solution and exact
target each compiled with exit zero on the committed Lean 4.30.0 / Mathlib
c5ea00351c28e24afc9f0f84379aa41082b1188f pin. All five transitive reports
(body_eq_corner_hull, corner_unique_objective, extreme_regular_objective,
all_endpoint_route and solution) contain only propext, Classical.choice and
Quot.sound. Full driver/solution compiler logs contain these reports without
compiler warnings. The separate target stub is not an admission in solution.

The publisher log was inspected through verdict, artifact upload, posted comment
and cleanup. The raw receipt records Proved: this is its authenticated readback,
not a separate direct platform or mission-root/leaf poll. Missing individual API
responses and full runner-log files are not fabricated.

## Exact repair and preserved first failure

The accepted source has 1247 lines / 54466 bytes, blob
c106008250409e7fc9eb3a3e8b187eb64d9f49e9, SHA256
80403727d5d0e7b3e11932dc937e76c3bdcd283c786a426bcfe44a7ea781aa87.
It matches the previously saved two-site proposal exactly. The update-self branch
is simplified, and the public let-bound set is reduced before introducing endpoint
hypotheses. Every declaration statement, hypothesis, metadata file and complete
1048-line accepted #315 prefix is unchanged. The public root PROOF gains dsimp only;
its body is not inaccurately called byte-identical. Forward/reverse patch checks
reproduce both source versions exactly.

The original run 35489239756 failed compilation before registration/submission.
Its source, request, diagnostics and failed-elaboration reports remain preserved.
The old handoff is archived verbatim. This is the SECOND compiler gate overall and
FIRST actual platform submission, with exactly ONE new trigger this continuation.
No source/metadata edit or extra trigger followed success. Local Lean/Lake was
unavailable; formal compilation is the pinned hosted evidence, not source/Python.

## Mathematical obligation now closed

For arbitrary real segment generators w_i, every two actual extreme points u,v
of the ORIGINAL coefficient sum Z can be connected by at most m nondegenerate
original exposed/extreme edges. Every visited point is extreme in the same Z.
No endpoint objective, regularity, Boolean injectivity, vertex catalogue, edge
oracle or short path is a premise. Zero, repeated, parallel, opposite and
rank-deficient generators, dimension zero, empty generators and equal endpoints
remain included.

The proof derives the finite set C of Boolean corner images and identifies
Z=convexHull(C), without declaring every corner a vertex. Removing an extreme u
leaves a convex set; the closed hull of C minus u excludes u. Strict separation
constructs an objective larger at u than all other corner images. The canonical
saturated corner maximizes over Z and must equal u. A nonzero tied generator would
produce a distinct maximizing corner by toggling its coefficient, a contradiction.
Thus the objective is regular and its whole face is {u}. Repeat independently
for v and apply accepted #315's ordered original-edge route.

The arbitrary-vertex objective and all-pairs zonotope route obligations are CLOSED.
The finite corner set is an existence-proof device, not polynomial-time code.
m counts generators, NOT original H facets. The completion construction still
needs controlled original-input generator complexity or a different quantitative
argument. No unrestricted Polynomial Hirsch, shortestness, new best classical
bound or historical-priority claim is made.

## Raw artifacts and supporting replay

All four original archive digests were recomputed; IDs/sizes/hashes are in
resume-publication-readback.json. All five frozen packet hashes match the verified
archive. The accepted #315 dependency's five hashes were also checked, and its
1048-line prefix matches exactly. Raw audit/manifest, full compiler logs, target,
driver, resolved request, verified aggregate and publisher receipt/comment are
separate from labelled derived summaries. Original ZIPs and full fixtures are in
the export. Existing first-failure files remain in repository history and tree.

The unchanged rational suite reran and passed clean three-script replay: all 502
endpoint pairs in 18 planar systems, 84 discovered vertices and 874 original
edge occurrences. It retains 143 nonvertex corner images, 138 duplicate Boolean
images, 272 parallel ties and 84 zero-length walks. Full support checks compare
25860 endpoint values, 40046 chamber values and 2100 event-face points. Four zero
cases, four selected larger cases through dimension64, 26 construction-disabled
saved audits and five forged inputs are included. Report11723 bytes and
fixture65977 bytes match their earlier hashes exactly. These are separate from
Lean verification and do not prove a parser, extracted algorithm or shortestness.

Reserved #210, other owned work, existing main files, the pin, strict0.10.6 guard,
workflows, allowlist, duplicate checks and credential separation were untouched.
