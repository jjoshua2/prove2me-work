# First gate failed in public wrapper; internal rank descent is clean

PR336 is OPEN/DRAFT, not a published or accepted theorem.
Target Hirsch.source_rank_reoptimized_original_routes.
Frozen tested proof e0dda913902528901bafb5b2c3049cef4dcb142b.
Source1067 lines/45630 bytes, blob39ab5cec2a687fdf40386c4571fb94278c5cf407,
SHA25645e9676e473e3ff1c61f4ec37b8044971ef2e5f86e94fb4baf1e2edc738c3fc8.
All three tested packet inputs remain unchanged after the gate.

Actual request5784984308 and acknowledgement5784987737 resolve this source to
run35790637527. Gate106957989213 succeeded. Verify106958053993 failed driver
compilation, exit1. Standalone solution and separate target-statement stages
were NOT reached. Publish106958349197 and report-verify106958348832 skipped.
No registration, submission, theorem/submission ID, receipt, ACCEPTED or Proved
result exists from this run. One hosted attempt, zero actual proof submissions.

The ONE reported error is at1059:19, the last public per-edge rank conversion.
The internal ht.right uses natural indices t.val+1 and t.val under the local R;
the expected statement uses t.succ.val and t.castSucc.val in inline finite filters.
All SIX internal reports, including decreasing_edge, target_rank_zero and the
complete ranked_route, use only propext, Classical.choice and Quot.sound.
Public solution still includes failed-elaboration sorryAx. No admission was
written, but clean internal helpers do NOT verify the complete packet.

A single-site repair is preserved separately, UNAPPLIED and UNCOMPILED. It names
both Fin projection equalities with rfl and unfolds local R/F/V wrappers in the
last simplification. Three lines replace one; no helper, signature, public
hypothesis, other root proof code, problem.json or explanation.md changes.
Proposed source1069 lines/45724 bytes, blob47af41dbdda528862c585c522c2452de918e1af3,
SHA2560ec12af9c127caf4d28df32997ad5607aa8cdb98c69722bf2613ce48f7372853.
Patch apply/check/reverse passes. That is not a compiler result; further errors
may appear. No second trigger was posted.

The new internal theorem constructs ORIGINAL edges decreasing a pointwise
reoptimized source rank, with no reset between acquisition phases. A derived
fixed target-exposing numerator and positive local normalizers define the rank
as DISTINCT normalized values below the CURRENT value on the actual target-lock
face. Face inclusion plus ratio decrease strictly lowers the old rank;
reoptimization cannot undo it. The route length is at most its initial optimum.
All original target locks remain. Exact finite H/hull equality and actual
endpoint extremality remain; no uniform polynomial bound or shortestness claim.
The separate finite order-cell solver is written/executed, not kernel-verified.

The eight-model exact suite and clean five-script replay passed159 routes/180
original edges,6346 order cells/6220 exclusions,33 savings versus full-spectrum
costs for the SAME numerator and six nonacquiring steps with rank descent.
Nine malformed controls fail. These small ranks/routes happen to match shortest
distances; no strict extra reoptimization benefit was observed. No universal
shortestness or comparison with #335's different rowwise budget is asserted.
A seven-vertex stress attempt timed out before completion and is excluded from
the success counts, not treated as an infeasibility certificate.

The supporting solver-file create_blob call was BLOCKED by OpenAI with an
undetermined safety status. It returned no blob. No retry, alternate encoding,
or alternate upload route was used. BOTH new scripts remain only in the local
export with three unchanged dependencies; they are not claimed committed.
The proof packet and this diagnostic preservation are independent of that write.

Only request artifact10721324553 exists:307 bytes, SHA256
 db513b8440f3acf910eea14ff604edeb9219311e5c77f8f3e60d3c2db7213ca7.
Its ZIP was downloaded/rehashed and exact resolved.json retained. The complete
decoded verifier log was read through cleanup; the full displayed compiler error
and all seven reports are extracted with timestamps removed. Selected exact
runner lines are separately labelled. No absent verified artifact is invented.

Durable handoff: research/SOURCE_RANK_ROUTES_HANDOFF.md.
Evidence: research/verification/source-rank-routes/first-attempt/.
Keep this PR draft. Preserve Lean4.30.0, Mathlib
c5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.8 and all publication guards.
#326,#282,reserved #210, accepted proofs and other owners remain untouched.
