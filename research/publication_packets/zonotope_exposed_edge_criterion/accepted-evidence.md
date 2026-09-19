# ACCEPTED: original exposed-edge criterion for finite segment sums

Theorem: `Hirsch.zonotope_exposed_edge_iff_tied_collinear`.
Theorem ID: `bb32ac53-d8ba-4e21-92eb-b7e5ec568c70`.
Submission ID: `f68818e2-63ce-40b3-a104-e63e9b71b454`.
Authenticated verdict: **ACCEPTED**. Trusted publisher live readback: **Proved**.
Do not resubmit this accepted packet.

## Actual request and exact verification

NEW top-level conversation comment 5742734506 on OPEN same-repository PR #312
began `/prove2me publish research/publication_packets/zonotope_exposed_edge_criterion`.
It was posted at 2026-09-19T14:39:18Z and read back. Bot 5742735713 resolved
proof `fefbdd9f422a7f1511713b4e2e80934087d40389` and run `35449401954`.
Verdict comment 5742760113 was posted at 2026-09-19T14:43:12Z and read back.
Trusted workflow/publisher main was `7ed199c915cd97afd65008f7ba60e171e28a39cb`.

Gate 105913822108, verify 105913848624 and publish 105914049575 completed
successfully; report-verify 105914050176 was skipped. Driver, solution and exact
target statement each compiled with exit zero at the committed Lean 4.30.0 /
Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f pin. All five transitive reports
(point_eq_cap_iff, line_face, segment_forces_line, endpoints_extreme, solution)
contain only propext, Classical.choice and Quot.sound. The complete driver and
solution compiler logs have no warnings. The separate target stub's intentional
placeholder is not an admission in the proof.

The verify and publisher job logs were read through their cleanup. The raw
receipt reports Proved; this is the publisher's authenticated readback, not a
second direct platform or mission-root poll. Individual API bodies not exported
by the publisher are not fabricated.

## Exact repair and preserved first failure

The accepted source is 454 lines / 18186 bytes, Git blob
`fdae9555c66329742f641c259e551f03edad132d`, SHA256
`cdf116eed7169dd2e8ea0cd53c58154393689e8c052c4fa6301c1682ddd9aad5`.
It matches the saved two-site proposal byte-for-byte. The only edits split a
layout-sensitive scalar_bounds proof term and expose a lambda-wrapped conditional
before the mass nonnegativity case split in line_face. All definitions,
signatures, mathematical assumptions, public root statement AND proof, accepted
helper bodies, problem.json and explanation.md remain unchanged.

First run 35448186683 failed before platform registration or submission. Its
original source, request ZIP, scoped diagnostic block and failed-elaboration
reports remain preserved. The former handoff is archived verbatim under
handoff-before-acceptance.md. Its pending-repair labels describe the earlier
state; the exact repair has now been applied and accepted. This was the SECOND
compiler gate overall and FIRST actual platform submission, with ONE new trigger
this turn. No proof or metadata changes followed success. Local Lean/Lake was
unavailable and compiler-host DNS failed; the actual compilation is the pinned
hosted evidence, not text checks or rational execution.

## Mathematical obligation now closed

For arbitrary generators w_i in R^d and arbitrary linear objective f, set
Z=sum_i[0,w_i] and F={x in Z: f(x)=sum_i max(0,f(w_i))}. The theorem proves:
F is a nondegenerate whole closed segment, exposed and extreme in ORIGINAL Z
with actual extreme endpoints, IFF the generators on which f vanishes contain
one nonzero representative spanning every such generator.

Every maximizing coefficient representation is accounted for: positive objective
values force coefficient 1, negative values force 0, and only ties remain free.
For collinear ties w_i=c_i*w_j, the endpoint displacement is
(sum_tied |c_i|)*w_j with a strictly positive coefficient. This constructs the
entire segment, including opposite and repeated directions. Conversely, a
maximizing corner b and every tied toggle b+w_i lie in the actual face; segment
parameters force collinearity, and a nondegenerate face cannot have only zero
ties. Exposed-face extremality gives actual original endpoints.

Repeated, opposite and zero generators, rank-deficient bodies, zero objective,
m=0 and d=0 remain included. No genericity, independence, vertex list, edge oracle
or short path is assumed. The criterion is not an assertion that every objective
produces an edge. It does not provide a generic objective sweep, arbitrary-endpoint
routing, a diameter bound, the translated #311 composition or a polynomial
original-H-row budget. Those remain separate obligations; no unrestricted
Polynomial Hirsch result or historical-priority claim is made.

## Preserved artifacts and supporting tests

All five frozen file hashes match the manifest and prepared source/metadata.
All four original ZIP hashes were recomputed: the previous request, new request,
verified packet and publication receipt archive. Their IDs, exact byte counts
and SHA256 hashes are recorded in resume-publication-readback.json. Raw logs,
audit, manifest, driver/target, resolved request, aggregate and receipt/comment
are separate from derived summaries. Original ZIPs and full fixtures accompany
the export; the repository preserves the extracted evidence and original failed
request. Full runner logs were inspected, not mislabelled as committed files.

The unchanged exact suite was rerun and repeated in a clean script-only workspace:
66 systems, 987 objectives, 37894 saturation checks, 2961 fractional cases,
236 edge-face instances and 751 singleton/higher-dimensional nonedges. Independent
planar hulls cover all 75 original planar edges. Five selected models reach d64
without full high-dimensional enumeration. All 27 discovery-disabled saved audits
and five forgery controls pass. The full 27430-byte report and 36496-byte fixture
match both historical and current runs byte-for-byte. These are supporting tests,
not Lean-extracted Python/JSON verification.

Other owned branches, reserved #210, accepted packets, existing main files,
toolchain pins, strict 0.10.5 guard, workflows, allowlist, duplicate safeguards
and trusted verify/publish credential separation are unchanged. The later
integration/evidence commit is distinct from the frozen proof SHA above.
