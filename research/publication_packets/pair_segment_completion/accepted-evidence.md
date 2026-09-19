# ACCEPTED: explicit pair-segment Minkowski completion

Theorem: `Hirsch.finite_hull_pair_segment_completion`.
Theorem ID: `f8820d5a-523e-42b2-a856-1ebfaf2c93db`.
Submission ID: `0307a57f-c4be-4cf2-ac81-80e04b743201`.
Authenticated verdict: **ACCEPTED**. Trusted publisher live readback: **Proved**.
Do not resubmit this accepted packet.

## Actual command and full verification

NEW top-level comment 5739508003 on OPEN same-repository PR #311 began
`/prove2me publish research/publication_packets/pair_segment_completion`.
It was posted at 2026-09-19T05:00:50Z and read back. Acknowledgement 5739509123
resolved proof `13930c76be3706447fc4d6dfd02f5ce4cf221a2e` and run `35422809743`.
Authenticated verdict comment 5739529634 was posted at 2026-09-19T05:04:50Z and
read back. Trusted workflow/publisher main was
`24b519ae1e7907a0d063cd36731d435da9918765`, not the candidate proof SHA.

Gate 105843448170, verify 105843466888 and publish 105843684007 completed
successfully; report-verify 105843684717 was skipped. Driver, solution and exact
target statement each compiled with exit zero. All five transitive reports
(compact_zonotope, translate_hull, support_witness, completion, solution) contain
only propext, Classical.choice and Quot.sound. Complete successful driver and
solution logs have no compiler warnings. The separate target stub's intentional
placeholder is not in the submitted proof.

The publisher log was read through verdict, archive upload, posted comment and
cleanup. The raw publication receipt records Proved. This is the publisher's
authenticated readback, not a separate direct platform or mission-root poll.
Individual platform API bodies absent from the artifacts are not fabricated.

## Exact repair and honest three-gate history

Accepted source: 283 lines / 11766 bytes, Git blob
`756319de8d9d6d2d00941f48a87ff9c572ce35e6`, SHA256
`ac3bddf6ecc4dd20b3360e75d759013620bee82593065481205e7fe966a85bb5`.
It is byte-identical to the previously saved two-helper proposal. This turn
changed only point_combo and replace_endpoint proof bodies: explicit scalar
finite-sum equalities and explicit pair/update reduction plus abelian-group
normalization. All signatures, hypotheses, the corrected public statement AND
root proof, problem.json and explanation.md are unchanged from the second gate.

First run 35420782170 failed on sum scope, update-lemma names and translate
membership. Its malformed, unregistered formal_statement required parentheses
in the second attempt; its bytes were not falsely described as unchanged.
Second run 35421714330 failed at the two helper bodies repaired here. Neither
failed run reached platform registration/submission. Their exact source/target
snapshots, requests, selected diagnostics and old handoffs remain preserved.
The new receipt supersedes historical failure statuses rather than erasing them.

This was the THIRD compiler gate overall and FIRST actual platform submission,
with exactly ONE new gate this continuation. No post-success proof/metadata
changes or additional publication triggers. Local Lean/Lake and compiler-host
DNS were unavailable; successful compilation is specifically the pinned hosted
evidence. Source matching and rational regression are not Lean verification.

## The construction now proved

For arbitrary real generators v_i, with n>0, define P=conv{v_i}, the explicit
ordered segment sum Z=sum_(i,j)[v_i,v_j], and Q={q: q+v_i in Z for every i}.
The theorem proves compactness and convexity of Z and Q, nonemptiness of Q,
and WHOLE-SET equality P+Q=Z. No summand, support equality, independence,
distinctness, full dimension or generic objective is assumed. Repeated/interior
generators, collinear families, n=1 and d=0 are included.

For every linear objective choose a maximizing generator k and select v_k on
each ordered slot (k,i), maximizing all other segments independently. The sum
z supports Z. Changing just slot (k,i) gives z-v_k+v_i in Z for EVERY i, so
q=z-v_k lies in the actual erosion and v_k+q attains Z's support in P+Q.
Convex-hull translation gives one inclusion; compact-convex strict separation
and these support witnesses give the reverse inclusion. This is not merely a
finite sample of directions or containment without equality.

The n^2 count is represented ordered SEGMENT SLOTS in the input GENERATOR count,
including diagonals and repetitions. It is not irredundant facets, a minimal
completion or a polynomial original-H-row budget. The packet proves no genuine
short Z-edge route; cube edges are not silently projected to original edges.
Accepted #309/#310 transfers can reuse this completed construction, but actual
sum routing and useful original-input complexity control remain separate.
No unrestricted Polynomial Hirsch, optimal diameter or historical-first claim.

## Original evidence and supporting replay

All five frozen file hashes were recomputed and match the raw manifest.
Five original ZIPs were recomputed: the two preserved earlier requests and the
three newly downloaded request/verification/publication archives. Exact IDs,
byte sizes and SHA256 hashes are in final-publication-readback.json. Raw audit,
manifest, full compiler logs, driver/statement, request, verified-artifact
aggregate and publisher receipt/comment are preserved separately from derived
readbacks. The full ZIPs and test fixtures accompany the export.

The unchanged Fraction-only regression ran again and in a clean script-only
workspace: 46 whole-body planar models, 1208 support witnesses, 6627 replacement
identities, 42189 coefficient bounds, nine selected instances through dimension
64, nineteen discovery-disabled saved audits and four rejected forgeries.
Complete report (12437 bytes) and fixture (33706 bytes) reproduce earlier bytes
exactly. These are supporting checks, not Lean-extracted code or a universal
JSON theorem. No accepted target, other owned branch, reserved #210, toolchain,
strict protocol guard, workflow, allowlist or credential separation changed.
