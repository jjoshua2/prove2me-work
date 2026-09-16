# PR #275: ACCEPTED affine-pair conditioning theorem

## Current state; do not resubmit

`Hirsch.affine_pair_conditioning_optimum` is ACCEPTED, theorem
`b2a9ab62-97c7-44d0-a44f-ef4d0d82d87c`, submission
`ffb93c00-4922-4f9a-9bc0-2ccde6c5f01b`. The trusted publisher's authenticated
live readback is Proved. Successful run `35137303939` froze proof head
`b02f89076b8f32a21cc79c2285544a9b1fa8fd55` and used trusted main
`ad88d6336b1d514cfd7ccd2a0a8e7949be0c2363`.

Read `publication_packets/affine_pair_conditioning/accepted-evidence.md`, the
unchanged raw `publication-receipt.json`, and `accepted-manifest.json`.
The earlier draft/version-blocker text is historical, not a reason to retry.
The prior handoff is archived verbatim in
`verification/affine-conditioning-2026-09-16/before-acceptance-handoff.md`.
Read current STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and LIVE PR
ownership before selecting more work; never modify or trigger reserved #210.

## What this continuation actually completed

It posted and read back real top-level publication comments, not a displayed
command or workflow_dispatch. First comment5702692752 started run35135897207:
compilation/audit passed, but the stale 0.10.3 publisher rejected the platform
version before any theorem/submission receipt. The official 0.10.4 release was
then inspected. Another agent's narrowly scoped #278 refresh was independently
reviewed, including exact upstream documentation hashes and all nine offline
guard tests. Strict mismatch checking, immutable artifact validation, duplicate
checks, actor restrictions and secret isolation remained unchanged.

After the refresh merged, comment5702875465 started the successful run. The
same 81-line proof compiled and audited without any proof or statement edit.
The three printouts use only propext, Classical.choice and Quot.sound. The
platform accepted the first actual submission and recorded live Proved.
A concurrent extra comment5702877332 produced run35137321661; it was observed
cancelled with zero jobs. No second platform submission came from that run.
No further trigger is needed or permitted for this accepted result.

Request, verified and publication ZIPs were downloaded and hash-checked; all
five frozen file hashes were recomputed. The source remains Git blob
ea86f01d8eb6ca445d50c0e5725eda40c00b44ca and SHA-256
9891ac1d52b21ca11914f4d80cb5e63862084bdc1b9d57b11053f892f84fda15.
Final publisher logs and bot verdict were read. Raw records are kept separate
from derived inspection summaries. The existing publisher checks accepted
source equality but does not export its raw target/source responses; do not
fabricate those responses. This is the publisher's live readback, not an
additional direct API poll by the chat. Local Lean/Lake remains unavailable;
compilation evidence is the pinned hosted gate, not Python tests.

## Exact mathematics and retained boundaries

For 0<e<1, the normal pairs (a,a+e*b) and (b,b+e*a) have minimum squared sine
at most e^2 over EVERY positive definite Gram matrix. X=Y=1,Z=-e attains it.
The public target proves precisely that algebraic all-metrics bound and optimum.
The positive-definiteness and parameter-range hypotheses are unchanged.

The full research note `AFFINE_CONDITIONING_BARRIER.md` realizes those pairs
at genuine facets of simple bounded octagons and higher-dimensional products;
a shallow coupling cut removes Cartesian-product structure while retaining
the obstruction. Exact short original routes show that bad conditioning is
not a graph-distance lower bound. These geometric and gain-balancing results
retain their WRITTEN/COMPUTATIONAL status; this acceptance does not silently
formalize them. Existing source/replay reports and datasets are unchanged,
and their earlier test counts were not rerun or claimed as new in this turn.

A universally well-separated affine chart is not an available premise for an
unrestricted Hirsch proof. Weaker normal-cone widths, projective maps, other
realizations and adaptive route-local arguments are not excluded. Nor does
this result prove the root or the arbitrary-carrier diameter leaf. Root/leaf
status in historical STATUS is not a fresh authenticated query here.

## Integration and next work

Preserve the accepted proof and both historical failed protocol attempts.
A stale original `manifest.json` source_commit identifies its earlier successful
compile; `accepted-manifest.json` records the actual accepted head, with the
same five source hashes. Do not rewrite the original frozen packet to erase
that history. Post-gate changes are evidence/handoff only and need no duplicate
proof submission. Check GitHub for the final integration head.

The next mathematical work should derive an actual adaptive route bound or
close a concrete unowned Lean obligation after reviewing the newest frontier,
not recreate this scalar obstruction or bypass the publisher's version guard.
#270's blocked companion and all other owned proof packets remain untouched.
