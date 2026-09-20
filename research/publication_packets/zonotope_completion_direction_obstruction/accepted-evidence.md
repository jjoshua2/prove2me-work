# ACCEPTED: original edge directions survive every compact zonotope completion

Target: `Hirsch.zonotope_completion_original_direction_obstruction`.
Theorem ID: `da8f6dad-a557-46a6-99ad-11ef6d2e5a9c`.
Submission ID: `eff892fe-babc-4217-ae49-2eb46336d233`.
Authenticated verdict: **ACCEPTED**. Trusted publisher readback: **Proved**.
Do not resubmit this packet.

## Actual new comment, exact proof and first-pass result

NEW top-level PR #319 comment 5750350283 began
`/prove2me publish research/publication_packets/zonotope_completion_direction_obstruction`.
It was read back. Acknowledgement 5750351204 resolved proof
7b1d1e7199de25855c5eadafe277a763796eaeb5 and run 35515972056.
The authenticated verdict in comment 5750368908 was read back.
Trusted workflow/publisher main was 56edc3105ff0dd1f373d28601b578cc0c441a7b2,
not the candidate proof SHA.

Gate 106091856386, verify 106091875525 and publish 106092094116 completed
successfully. Report-verify 106092094750 was skipped. Driver, solution and exact
target statement each compiled with exit zero. All five transitive reports
(projection_self, inherited_edge_direction, completion_lower_bound,
antipodal_direction_lower_bound and solution) contain only propext,
Classical.choice and Quot.sound. Driver/solution logs contain no Lean warnings.
The target stub's intentional placeholder is not in the submitted proof.

Both job logs were inspected through cleanup. The raw publisher receipt records
live Proved. This is publisher-authenticated readback, not a second direct platform
or mission-root/leaf poll. Individual authenticated API bodies and complete
runner-log files not exported here are not fabricated. The actual raw compiler
logs, audit, manifest, request, verified aggregate and publication receipt are
committed separately from derived summaries.

This was the FIRST compiler gate and FIRST platform submission, exactly ONE new
publication trigger. The source remained unchanged. Local Lean/Lake was absent
and toolchain DNS failed, so formal compilation is specifically the pinned hosted
evidence; source checks and rational tests are not Lean verification.

## Exact mathematical progress

Let P=conv(C), with C any finite set of real points, and let Q be nonempty compact.
Assume ACTUAL whole-set equality P+Q=Z, where Z is the coefficient zonotope
sum_i[0,w_i]. Every nondegenerate whole exposed edge direction of P must occur
among nonzero generators of Z. From r pairwise distinct unoriented original edge
directions the proof constructs an injective selection of parallel generators,
proves r<=m, and constructs opposite actual vertices of Z between which EVERY
feasible-point walk through nondegenerate whole exposed Z segments has at least
r steps. No direction-inheritance, matching, endpoint-objective or path-cost
oracle is supplied. Q convexity is not needed. C need not be a vertex catalogue.

The new proof annihilates an original edge direction by a transverse map and
regularizes on projected generators and finite off-edge corner gaps. Were that
direction absent, the resulting objective would simultaneously be regular on Z
and constant on the original edge. Compactness supplies one maximizing q in Q;
two distinct translated edge endpoints would maximize on Z, contradicting its
singleton regular support face. This is objective construction, not arbitrary
polytope-edge projection. Accepted #317 then supplies the intrinsic lower bound.

Finite-hull structure, nonempty compact Q, genuine Minkowski equality and the
selected family of nonparallel original exposed edges remain explicit hypotheses.
The lower bound concerns completion diameter, not the original summand. Path
existence is separate (accepted #316 for zonotopes). No shortestness, original-H
polynomial upper bound, or Polynomial Hirsch counterexample is claimed.

The separate written note proves the 2d-facet triangular deformed cube has
2^d-1 edge directions and original diameter d. It applies the general theorem to
EVERY completion of that family. Its facet/count/translation steps remain written
mathematics and supporting finite tests, NOT additional Lean theorems in this
packet. This distinction is retained in the handoff and final report.

## Exact reuse and local-only history

The accepted 945-line / 39901-byte source equals the earlier local candidate:
blob 791a71ce939f7f6181dcd3a51681ef4f263a55b4;
SHA256 8ffc6b7da55ed39449ee1a21f8a0bdb38c2b4d56b592c940ef52bc00ce0aae05.
The 629-line #317 prefix and 81-line #313 regularization section are byte-identical;
both accepted dependency packets' five manifest hashes were checked again.
Their public targets were not resubmitted. No assumed helper replaces a proof.

Before this first request, historical local-only status wording in problem.json
and explanation.md was refreshed. The source, exact public type and mathematical
hypotheses did not change. The original local bundle retains the earlier metadata,
notes and unposted draft. No metadata or source change followed the gate.

Fresh main/queue and exact-target searches found no competing inheritance packet.
Coordination 5750301673 on #318 was posted and read back. #318's rich-inventory
compatible-cube-lift lower bound is a distinct accepted theorem, not repeated here.
Reserved #210 and all other owned proof branches were untouched.

## Raw artifacts and supporting replay

All THREE original downloaded ZIPs were independently rehashed:
request 10607120861, 315 bytes,
7c7a838c8bb75035d4aa788bc47b5a913320f24f5877d3cb96d0c49d94e258b8;
verified 10606502270, 28740 bytes,
87324fba70e35912d0116edd0ce39be49dba0dcfb81fb8c9da57339232905a92;
publication 10607090999, 918 bytes,
1213940133204684d38b8a553925173713d269fac9270aa9dd8398acb999bfb4.
All five frozen file hashes match the original verified archive and prepared files.
Full original archives, complete test outputs and the original local-only bundle
accompany the export. Repository compact summaries are not called full fixtures.

The unchanged 293-line test script reran, then reran in a clean script-only workspace.
Both full outputs equal the previously saved bytes: report 9885 bytes,
SHA256 d751aa51d4889c18385cc796e9b20d7efe1c58d92b3017b2b3e9eba350d3d736;
fixture 303297 bytes,
SHA256 429b220f739e3b00fff45a3351b078bead61a51f3b5b9fac3bf094a85c00d206.
Tests cover 18 complete small original-H models, 3822 square bases, 378 vertices,
963 edge occurrences, 46422 whole-support comparisons and 4092 endpoint distances.
There are 28 whole planar Minkowski completions, 64 selected larger edge checks,
82 construction-disabled saved-edge audits and seven malformed controls.
These are not Lean-extracted software, a verified parser or extra formal theorems.
The script's historical uncompiled-status string remains for exact regression;
this raw receipt supersedes that status rather than changing the test bytes.

Lean 4.30.0 / Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f, strict protocol
0.10.6, workflows, allowlist, duplicate guards and credential isolation remain
unchanged. Consult live PR metadata for later evidence and merge SHAs.
