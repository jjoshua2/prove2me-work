# First gate: five helper audits clean; one tight-row identity needs reduction

PR #341 remains OPEN/DRAFT and unmerged. Target:
Hirsch.original_row_radial_max_envelope.
Tested proof: 3db31f9347cdb9e1b3aab9cd27d57dcba58917ab.
Main at gate: ec4bf56356953c53184beb61a49482c13ea8e9b1.
Source: 560 lines / 24547 bytes, blob f2ace0469aaa16c2254d137c0a0b7813018da303,
SHA256 716e85e67fa5de7fb09a4bbc1f9b6d73ea420acb8d5b94d7d88845062ef2dc9e.

## Actual gate result

New top-level request 5806137779 and bot acknowledgement 5806139188 bind run
35945514083 to that exact proof. Gate 107462443222 succeeded; verifier
107462479535 failed driver compilation at 185:8. Standalone solution and the
separate exact target statement were not reached. Publisher 107462855431 and
report-verify 107462855028 were skipped. This was the first hosted attempt.
No registration, actual proof submission, theorem/submission ID, verified
artifact, publisher receipt, ACCEPTED or authenticated Proved was produced.

Five named reports contain only propext, Classical.choice and Quot.sound:
epigraph_iff, strict_on_body, ray_threshold, non_target_active and exposed_edge_row.
The dependent vertex_envelope, vertex_injective and public solution reports
retain failed-elaboration sorryAx. No admission was written in the proof.
These independent clean helper reports do NOT verify the complete packet.

## Exact local repair proposal, not applied and not compiled

The sole displayed error is in scaled_tight. After congrArg, the hypothesis hh
still displays the lambda applications

    (fun z => z * a) (f y / a) = (fun z => z * a) (b - f v).

The cancellation rewrite does not find the beta-reduced product. Insert exactly
one proof line immediately before the existing rewrite:

    change (f y / a) * a = (b - f v) * a at hh

The patch adds one line and deletes none. It preserves every declaration,
accepted helper, complete public root, metadata file and explanation. Proposed
source: 561 lines / 24594 bytes, computed blob
5aa85241c966d6a2ebfc355f0f911f1a66754e22, SHA256
2cc1309ad076230fb3af3dada0d4059764c41dbf909e856be17b7dfeec863c5f.
It is UNAPPLIED to the publication source and UNCOMPILED. Patch application and
reversal were checked in a fresh scratch Git repository. Further compiler errors
may appear. No second gate or post-gate proof/metadata edit occurred.

Patch: research/verification/radial-original-row-envelope/first-attempt/
proposed-beta-reduction-repair.patch. Resume this SAME PR after fresh live
ownership/pending checks, local compilation where available and one prepared
complete pinned gate. Do not rename the target or weaken its hypotheses.

## Mathematical progress and limits

The candidate handles arbitrary ambient dimension, exact finite-hull/original-H
equality and an actual target vertex. It derives a strict exposure on the whole
body. For positive inverse height a, original rows transform exactly into
A_i(y)<=a*(b_i-A_i(v)). Target-tight rows remain directional constraints; the
positive-slack rows give an attained positive maximum and exact radial threshold.
These components now have independent standard-only reports.

The original-edge witness also has a clean report: an original exposed segment
avoiding the target has an ORIGINAL row slack at the target and tight at both
endpoints. This supplies a label that can be charged, not a bound on repeated
charges. Exact retention of all vertex tight labels and normalized vertex
injectivity still depend on the failing tight-row identity. The complete theorem
is not yet verified. No constructed polynomial route, graph isomorphism,
face-lattice theorem, numerator optimization or unrestricted Hirsch result is
claimed. At most m affine pieces need not give polynomially many vertices.

## Reproduction, provenance and the blocked supporting upload

The proof and formal statement are unchanged from the user's supplied local-only
candidate. Metadata provenance and explanation lifecycle wording were updated
before this first gate. All copied helper bodies match the downloaded accepted
#340 verified source. The previous local-only session had no PR or submission.

Fresh standalone rational execution reproduced all FOUR supplied outputs exactly.
Small scope: 13 complete H catalogues, 181 non-target vertex/target observations,
1946 tight-row identities, 281 original non-target edge/target witnesses and
1060 radial probes; 12 controls rejected. Large scope: selected cube points and
directions in dimensions 8/16/32/64, with 24 vertex observations and 160 probes.
The large data are not complete catalogues or graphs; their rank checks concern
selected subsets. Python and JSON are not kernel-verified.

The attempted GitHub.create_blob upload of scripts/test_radial_row_envelope.py
was blocked by OpenAI because its safety status could not be determined. No
script blob was returned or committed. That upload was not retried or routed
through another action. The original user-supplied archive and local test files
are preserved; the repository records only derived test results and identities.
This block did not affect the already committed Lean packet or its actual gate.

Only request artifact 10786009631 exists: 313 bytes, SHA256
11b02eb860e35393a11532d8ed51e015da481aed967828a19cba3c3c146323f1.
Its original ZIP was downloaded/rehashed, and exact resolved.json is preserved.
The full decoded verifier log was read through cleanup. Stored diagnostics
contain the complete displayed error and all eight reports, with timestamps,
one unused-simp warning and setup/cleanup omitted. Selected runner excerpts
are not a full raw runner archive. No missing artifact or API body is invented.

No local Lean/Lake/Elan or checked installation/cache was available; toolchain
hosts failed DNS. Text checks and rational tests are not compilation. Keep
Lean4.30.0/Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.8,
other owners, accepted bytes and verifier/publisher secret separation unchanged.
Handoff: research/RADIAL_ORIGINAL_ROW_ENVELOPE_HANDOFF.md.
