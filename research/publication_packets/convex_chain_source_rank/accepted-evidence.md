# Accepted: exact source rank for strict convex chains

## Frozen proof and actual publication

Target: Hirsch.strict_convex_chain_exact_source_rank.
Theorem: e5c0158b-f340-4262-865a-7f6936b83db1.
Submission: a2f3ea44-ec31-41a9-a4da-d3929d79340c.
The unmodified trusted-publisher receipt records ACCEPTED, registration REUSED,
and live_status Proved. Proved is the publisher's authenticated readback, not an
independent platform or mission-root poll by this continuation.

Accepted submission commit: 223b5abfc8666393b2b60bec387f4e49d3f626b8.
Initial complete verified proof: de2e0175d0db46ecc13ccbe6c003efd535da6417.
The source and metadata at those commits are byte-identical. Source351 lines /
15120 bytes, blob668d5a54143923d16c293393c6affb3ab2759d16, SHA256
 dc2a830c3da548edd4d1949235fbb5c0eb4f4178e9a5665b5744b74fe5048afe.
Trusted main at resume: 6ee1612a05cede29039c4728825b7d5d255f14a8.

New top-level request5801952351 and acknowledgement5801955039 resolved run
35912718942 to that exact accepted submission commit. Verdict5802016156 at
2026-09-23T20:01:26Z records the actual acceptance. All were read back.

## Existing registration reused, not replaced

The previous run35895877060 returned PUBLISH_PENDING/QUEUED for registration job
cfbe3736-58f8-4c07-9de0-63147127b046. Its raw receipt, comments and full previous
handoff remain historical evidence. This continuation used the existing guarded
publisher with unchanged target name, statement, environment and proof. The new
receipt says REUSED: the publisher found the existing exact theorem, then made
the first actual proof submission. No new problem registration was issued by
that REUSED path. This is not an independent fresh poll of the former job ID.

There were three complete hosted compiler runs overall: the original failed run,
the passing run that returned pending registration, and this passing resume.
There have been two complete passing gates and one actual proof submission.
Only one new publication command was posted in this continuation. No proof,
metadata, script, toolchain or workflow edit was made to obtain acceptance.

## Complete verification

Driver, standalone solution and exact target statement each compiled with exit0.
All six named reports in BOTH full proof logs contain only propext,
Classical.choice and Quot.sound, including public solution. No sorryAx remains.
The separate target-statement placeholder is not proof evidence.
Gate107356343122, verifier107356413000 and publisher107356812856 succeeded;
report-verify107356814411 was skipped. Lean4.30.0, Mathlib
c5ea00351c28e24afc9f0f84379aa41082b1188f and strict protocol0.10.8 are unchanged.
Actual compilation evidence is hosted; no local Lean execution is claimed.

The earlier repair added only four spaces in two annotations. That repaired
source was not modified here. The initial failed source and all nine displayed
diagnostics from run35886406394 remain preserved. publication-pending.md and
first-gate-evidence.md are historical snapshots, superseded in status by this
acceptance record, not deleted or rewritten to erase their outcomes.

## Exact mathematical result and hypotheses

For real arrays w,a indexed by Fin(n+1), assume StrictMono w and strict
triple-secant convexity:

    (a_j-a_i)(w_k-w_j) < (a_k-a_j)(w_j-w_i) whenever i<j<k.

For source k, let U(t,k) be the DISTINCT values a_i+t*w_i above a_k+t*w_k.
The theorem proves min_t |U(t,k)| = min(k,n-k). It derives a single M>0,
independent of k, with |U(-M,k)|=k and |U(M,k)|=n-k. For every source one of
these two tilts attains the minimum. A derived translation makes all chosen
heights positive. Reciprocation and adjoining target zero then give exact lower
rank min(k,n-k)+1 and twice-rank <= n+2.

The universal lower bound and attaining tilts are outputs, not a small-rank
hypothesis or a supplied oracle. Strict convexity and ordered abscissas remain
explicit and essential. Signed ordinates, singleton/two-point chains, endpoint
sources and cross-side coincidences remain included.

This is the accepted FINITE-CHAIN theorem. The original-polygon chart, support
lines, ordinary-edge and facet interpretation in explanation.md are separately
written and tested arguments, not additional Lean conclusions of this packet.
No arbitrary-dimensional polynomial ordinary-edge bound, changing-numerator
result, implementation extraction or historical-priority claim is asserted.
The mission's uniform original-input bound remains a separate obligation.

## Fresh exact tests and durable evidence

All three unchanged test scopes reran: small,20 seeded irregular polygons, and
the64-vertex/eight-target planar scope. All SIX complete output files reproduce
their previous bytes. The24 configurations contain2030 routes/11464 original-edge
occurrences,1840 unique transitions and1084 nonacquiring unique steps. Ten distinct
malformed/premise controls are rejected. Small/random comparisons cover9194
reference sweep cells. The64-vertex case is planar, not dimension64. Python/JSON
and the written geometric bridge are not kernel-verified.

The supplied previous pending-evidence archive was independently rehashed and its
existing inspector rerun:73 manifested files,105 content checks and8 corrupted-
copy controls pass. This is a stored-evidence check, not server authentication.

All twelve new raw verified files, two raw publisher files and the exact resolved
request are retained in resumed-publication/. Three original downloaded Actions
ZIPs match the returned digests, all fifteen extracted members match, and all five
frozen input hashes are unchanged from the previous passing gate. Complete proof
logs also reproduce their previous bytes. The raw packet tree is
29dea66b4e96aa1426500d331c5b9934d917643e; the verified tree is
820517827aa04bcee708c4cc55bf447d21507a3e; receipt tree is
502021a9d9986283f28c34fe1c6c494fbc922ebf. Each matches local Git hashing.

Both complete decoded runner logs were read through cleanup. The stored runner
excerpt is selected, not a full raw runner archive; complete compiler logs remain
unchanged. Missing individual platform API bodies are not reconstructed.

The export preserves both old failure/pending histories, original archives, full
fixtures, unchanged scripts and a reproducible offline checker. Offline hashing
and corruption checks do not execute Lean or authenticate arbitrary receipt JSON.
Current repository handoff: research/CONVEX_CHAIN_SOURCE_RANK_HANDOFF.md.
Check live PR lifecycle before any remaining integration; do not resubmit.
