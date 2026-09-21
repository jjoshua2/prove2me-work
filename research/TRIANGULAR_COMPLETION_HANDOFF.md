# Triangular all-completion lower bound: verified proof, publication blocked

## Current result (September 21, 2026)

PR #320 remains OPEN/DRAFT on proof/triangular-all-completion-exponential.
The entire standalone packet now compiles and passes transitive axiom auditing.
Publication is blocked by the trusted publisher's strict protocol-version check,
not by the Lean proof. No registration, submission, ACCEPTED or Proved result
was produced by this run. Do not label a local/hosted compiler PASS a platform verdict.

Target: Hirsch.triangular_all_zonotope_completions_exponential.
Packet: research/publication_packets/triangular_completion_lower_bound.
Frozen verified proof SHA: 2efb69e4e25165bfd2a5abc2fe2673d950114ab9.
Source blob: d601bb6d8c223609a9b9b269385421f4e0bbc39b.
SHA256: 0d66d238760cd88b933429d49c0d421a04af8c4c66f13c6ad532feff625b4fb2.
The source is 1649 lines / 68361 bytes. Any later evidence-only branch head is
not a new verified proof SHA; preserve this source and metadata byte-for-byte.

## Actual request and last observed execution

Coordination comment 5763614415 was posted after live main, PR heads, ownership,
conversation and empty review-thread checks. Applied only the saved two-site patch
and read the resulting exact diff/blob back before the publication trigger.

NEW top-level publication comment 5763775688 was posted and read back by ID.
Its first line was:
/prove2me publish research/publication_packets/triangular_completion_lower_bound

Bot acknowledgement 5763779304 resolved the frozen proof above to run 35624792380.
The issue_comment workflow's trusted main SHA was
 d3d722007211c6fbb9d28417ef7a1c1b5a47c585, not the proof SHA.

Gate 106416398632: success.
Verify 106416491690: success; driver.lean, solution.lean and statement.lean all exit 0.
Publish 106416979748: failure before theorem lookup / registration / submission.
Report-verify 106416982103: skipped.
No-receipt bot comment 5763800712 was read back; it is not an acceptance verdict.

Publisher diagnostic at 2026-09-21T16:20:34.2520449Z:
"Platform skill version changed; refresh the skill before publishing."
The trusted VersionCheckedAPI.refresh guard still requires exactly 0.10.6.
The actual returned version is not exposed in the log. No receipt files or
publication-receipts artifact were produced. No independent platform poll occurred.

## Full proof and artifact verification

Lean 4.30.0 was reported by the hosted pinned environment; Mathlib remains
c5ea00351c28e24afc9f0f84379aa41082b1188f. The secret-free verifier compiled the
complete driver and standalone solution. All SIX explicit reports, including
exposed_line, minimal_eq_body, exponential_completion and the full public solution,
now contain only propext, Classical.choice and Quot.sound. No sorryAx remains.
The statement.lean warning concerns only the separate target-statement placeholder;
it is not used as the proof. The inherited unused-simp warning is unchanged.

Downloaded and independently rehashed both raw ZIP artifacts:
- request 10651081845: 315 bytes; SHA256 df9f79a4c8cc0152bd53114779c6489709cb36ba6585440cd1892de2ba7e716a;
- verified packet 10651296899: 41487 bytes; SHA256 228d87f5c292a93570614b386f22a47fcd22f5b1e86c89f0434ed8ea592b7c09.

All five frozen manifest-file hashes pass recomputation. The artifact solution is
byte-identical to the committed repair; driver equals solution; problem.json and
explanation.md retain their original Git blobs. The public solution's type exactly
matches the target text after replacing only the theorem name. All declarations,
hypotheses, accepted namespace bodies and full public proof assembly were preserved.

## Durable evidence and original failure

research/verification/triangular-completion/repaired-attempt/ contains the raw
resolved request; all 12 files unpacked from the verified artifact, including
complete compiler logs, manifest and packet-audit; source/artifact checks; and a
DERIVED run-readback plus explicitly scoped runner-log diagnostic excerpt.
The full decoded runner logs were read but are not represented as a committed raw
runner archive. The two original raw ZIPs also accompany this continuation's export.

The first failed source and diagnostics under research/verification/triangular-completion/
remain untouched. Original proof 9c4c8c1e046759df90e02115d9cc3847273118fb,
evidence head c0a282ae0e1b646bbcfe210fccb08fc736fe9896, trigger 5750632491,
acknowledgement 5750633628 and failed run 35518652354 remain historical evidence.
The previous handoff and mathematical note are copied into repaired-attempt/.
The saved patch changed only finite-index equality proofs in supporting_line
and minimal_eq_body. No source or metadata edit followed the new hosted gate.
Local Lean/Lake was unavailable; source checks were not misreported as compilation.
The earlier rational regression remains supporting evidence, not a new rerun here.

## Mathematical statement and unchanged limits

For 0<e<1/2, P in dimension n+1 has exactly 2(n+1) DISPLAYED ORIGINAL inequalities:
0<=x_n<=1 and e*x_(i+1)<=x_i<=1-e*x_(i+1) for i<n.
The verified proof derives the entire finite-hull identity and constructs 2^n
pairwise nonparallel genuine original exposed edges, then applies accepted #319.
For EVERY nonempty compact Q and ACTUAL whole-set equality P+Q=sum_i[0,w_i], it
proves 2^n<=m and constructs opposite actual completion vertices requiring at least
2^n steps along nondegenerate whole exposed completion segments. Q need not be convex.
No vertex catalogue, edge family, direction matching or count oracle is assumed.

The lower bound concerns the COMPLETION, not P. This is not a Polynomial Hirsch
counterexample or a solution of the mission. A formal facet-lattice count, the
stronger full 2^(n+1)-1 direction count, exact original shortest diameter,
translation extension and asymptotic domination theorem are not claimed.

## Exact next blocker and ownership

Freeze the verified proof and packet metadata. Resolve the official protocol
compatibility change in a SEPARATELY REVIEWED trusted-main change; do not change
or weaken the 0.10.6 guard, workflows, allowlist or credential separation on this
proof branch. The new version must be obtained from official evidence, not guessed.
Do not request credentials or repeat speculative Actions runs. After compatibility
is actually resolved, recheck live ownership and pending/accepted submissions before
any later authorized publication retry of these identical proof bytes.

PR #320 deliberately remains draft pending publication. Do not merge it as accepted.
Do not resubmit accepted #319, reserved #210, or #282's separately owned positive
triangular original-route/classification work. No unrelated PR was changed.
After this publication obligation is closed, prefer an unowned positive ORIGINAL
surviving-edge or repeated original-row charge bound after reading live handoffs
and counterexamples; do not manufacture equivalent completion obstructions.
