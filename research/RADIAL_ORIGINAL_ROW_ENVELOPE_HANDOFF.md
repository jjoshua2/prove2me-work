# PR #341: radial original-row envelope — first gate failed at one site

Read the five project instructions and LIVE heads/comments before continuing.
The preceding local-only handoff is superseded by this actual PR and run. Continue
THIS target, not accepted #340 or obsolete #320. Respect #326, #282, reserved
#210 and changing-numerator ownership.

Branch: proof/radial-original-row-envelope.
Packet: research/publication_packets/radial_original_row_envelope.
Target: Hirsch.original_row_radial_max_envelope.
Tested proof: 3db31f9347cdb9e1b3aab9cd27d57dcba58917ab.
Source: 560 lines / 24547 bytes, blob f2ace0469aaa16c2254d137c0a0b7813018da303,
SHA256716e85e67fa5de7fb09a4bbc1f9b6d73ea420acb8d5b94d7d88845062ef2dc9e.
Main at gate: ec4bf56356953c53184beb61a49482c13ea8e9b1.
Later evidence commits do not replace this tested identity.

## Actual result and exact next proof action

Coordination5806076765; request5806137779; acknowledgement5806139188;
run35945514083. Gate107462443222 succeeded; verifier107462479535 failed driver
compilation with one error at185:8. Standalone solution/statement not reached.
Publisher107462855431 and report-verify107462855028 skipped. One hosted attempt,
zero registrations/proof submissions; no IDs, ACCEPTED or Proved result.

Five reports are standard-only: epigraph_iff, strict_on_body, ray_threshold,
non_target_active and exposed_edge_row. vertex_envelope, vertex_injective and
solution retain failed-elaboration sorryAx. No admission was written; the full
packet is not verified.

The one-line repair is under first-attempt/proposed-beta-reduction-repair.patch.
Insert before the failed division-cancellation rewrite:

    change (f y / a) * a = (b - f v) * a at hh

This exposes the beta-reduced congrArg equality. It adds one line, deletes none,
and leaves all declarations, accepted helpers, the entire public root, metadata
and explanation unchanged. Proposal561 lines/24594 bytes, computed blob
5aa85241c966d6a2ebfc355f0f911f1a66754e22, SHA256
2cc1309ad076230fb3af3dada0d4059764c41dbf909e856be17b7dfeec863c5f.
The proposal is UNAPPLIED to publication source and UNCOMPILED. Apply/reverse
checks passed in a scratch repository, not Lean. Further errors may appear.
After fresh live checks, apply this exact repair, compile locally where available,
and use one prepared complete pinned gate on the SAME PR. No second gate was
posted in this continuation and no post-gate proof/metadata edits were made.

## Mathematical scope and next real gap

The all-dimensional candidate derives strict target exposure, exact original-row
radial feasibility and positive attained thresholds; retains vertex tight labels
and normalized vertices; and derives an original positive-slack row supporting
each non-target exposed edge. The edge witness and threshold have clean helper
reports, but complete vertex retention/public assembly need the repair.

Exact finite-hull/H equality and actual target extremality remain explicit.
No polynomial route or repeated-charge bound is concluded. The intended next
mathematical gap is controlling repeated original-row charges along a constructed
ordinary-edge route, not counting an expanded envelope-vertex inventory.

## Evidence and supporting-script block

Packet first-gate-evidence.md and first-attempt/ preserve exact failed inputs,
resolved request, complete displayed error/all eight reports, patch and labelled
derived readbacks. Only request artifact10786009631 was produced,313 bytes,
SHA25611b02eb860e35393a11532d8ed51e015da481aed967828a19cba3c3c146323f1.
The original ZIP and complete local test outputs are in the export. Extracts are
not full raw runner archives; no verified/publication artifact was fabricated.

GitHub.create_blob for the supplied supporting script was blocked by OpenAI.
The script was NOT committed, retried, or uploaded through an alternate route.
Do not misread the local work tree or previous changes.patch as evidence that
scripts/test_radial_row_envelope.py exists on this branch. Preserve the block;
this handoff does not authorize a workaround. The user already has the original
archive containing the unchanged script and its complete fixtures.

Fresh execution reproduced all four supplied outputs:13 small full catalogues,
181 vertex observations,281 edge/target witnesses,1060 probes and12 controls;
selected8/16/32/64D cases add24 vertex observations and160 probes, not complete
catalogues or routes. Python/JSON are not kernel-verified. The original local-
only archive has its own historical validator; it does not validate the new PR.

No local Lean/Lake/Elan/cache was available and toolchain DNS failed. Retain
Lean4.30.0/Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.8,
all other ownership, accepted input bytes and verifier/publisher isolation.
