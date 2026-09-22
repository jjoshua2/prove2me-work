# Lean verified; Prove2Me publication blocked before submission

Target: Hirsch.target_determining_row_budget_routes.
PR #330 remains OPEN/DRAFT, unmerged. This is not an acceptance receipt.
Frozen proof: 4493c3f97ff50f04bead9d5c3596bc4e3eeb7af4.
Trusted main: bfacf0fca8aac4205569070d224ee8cc736ef38d.
Source1343 lines/59088 bytes; blob4202603709626ec3c9ad0bf9922f5c2affbdae53;
SHA2561973de8f135e4c4fe4e58088594627fd2a113ab8067372b6701274af44d1816b.
No source or metadata edits followed the complete passing compiler gate.

## Actual request and distinct results

Coordination5773513102 on #329, actual NEW top-level request5773867317,
acknowledgement5773869906, run35708263100. All were read back.
Gate106682338925 and verifier106682393814 succeeded. Full driver.lean,
standalone solution.lean and separate target statement each exited zero.
All EIGHT named proof reports in EACH full proof log contain only propext,
Classical.choice and Quot.sound. No sorryAx remains in those reports.
The separate statement-only placeholder is not proof evidence.
Hosted Lean4.30.0/Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f are unchanged.

Publisher106682876284 FAILED at VersionCheckedAPI.refresh with:

    Platform skill version changed; refresh the skill before publishing.

The strict trusted-main guard expects0.10.7 and raised before theorem lookup,
registration or proof submission. The returned refresh JSON/version was not
logged and is unavailable. No theorem ID, submission ID, receipt, ACCEPTED or
Proved result was produced. Bot comment5773891203 at2026-09-22T09:05:53Z says the
job finished without a receipt and was read back. Report-verify was skipped.
This was the FIRST complete hosted compile and ZERO actual proof submissions.
No additional trigger, independent platform/root poll or guard bypass occurred.

A separate read of the OFFICIAL prove2me/prove2me_workspace SKILL.md at immutable
commit d26f4afe39dc674c3c91195a80876f0cff354b33, blob2f03fc8448f16fe79af91e8c6590ea972a75c9ff,
shows metadata.version0.10.8. That is official file evidence, not an invented
value from the missing refresh response and not an API compatibility approval.
A SEPARATELY reviewed official compatibility update is required on trusted main.
Do not suppress the guard, accept arbitrary versions, edit it on this proof
branch, change Lean/Mathlib pins, or request credentials. The proof needs no
mathematical repair; resume this same target after compatibility and duplicate
checks, then follow the actual future publisher evidence.

## Verified mathematical content and limits

For exact finite H/hull equality in ambient d with m ORIGINAL inequalities and
actual extreme endpoints u,v, let G be original equations shared by both endpoints
and T the target-tight labels missing at u. Derive S contained in T, |S|<=d,
whose equations together with G have trivial homogeneous kernel. Minimize the
actual row-level weight sum over ALL such determining completions of size<=d.
Construct a route of whole nondegenerate IsExtreme ORIGINAL segments through
actual vertices, preserving every acquired target row, of length at most that
minimum selected weight. The SAME route satisfies K*min(d,m-d) when only its
SELECTED rows have at most K+1 actual vertex values. Unselected rows are unrestricted.

Selection, determining property, phase lengths and complete route are derived,
not assumed as a graph, active basis, residual rank, small catalogue or cheap
phase. Shared equations cost nothing; selected labels are charged once. Minimum
row budget is not shortest path. Exact H/hull equality and actual endpoints stay
explicit. The selected-level implication retains its antecedent, and the general
minimum weight can remain exponential. No unrestricted Polynomial Hirsch claim,
all-facet nonrevisiting, global monotonicity or efficient H-to-V/selection theorem.
Redundancy, nonsimple/lower-dimensional bodies, d0 and equal endpoints remain.

## Reuse, tests and evidence preservation

The accepted #329 namespace prefix972 lines/41010 bytes and #325 directions and
small_active_rows bodies458/2219 bytes are byte-identical. Both five-file
manifest checks pass. Earlier detached upload transcription mismatches were
caught before the first commit and were neither compiled nor submitted. The
single committed candidate passed without a Lean repair. The public type
exactly matches problem.json. Local Lean/caches/DNS were unavailable; no local
Lean compilation is claimed.

19 exact hulls and701 routes give817 original-edge occurrences versus816 shortest
edges. The one nonshortest route,37 multiedge phases and18 nonacquiring steps
remain.351 endpoint cases have smaller budgets than the prior all-missing sum;
4171 determining candidates are checked. Ten malformed controls fail. Four cube
cases through64D check120 more original edges and four additional controls.
The extra exponential-inventory row is explicitly REDUNDANT; its binary level
count is a written formula application, not large graph enumeration or an extra
Lean instance theorem. No irredundant-facet lower bound is claimed.

Clean five-script replay reproduces all five complete reports/fixtures/control
outputs byte-for-byte. Full outputs accompany the bundle and regenerate; the
repository test summaries are labelled derived. Python/JSON are not kernel-
verified. The export-only inspector passes33 stored-evidence checks and rejects
nine corruptions, without compiling Lean, authenticating arbitrary JSON, or
polling the platform. It explicitly rejects invented acceptance/identifiers.

Both raw archives were downloaded and rehashed. All12 unmodified verified files
and the exact request are preserved, with full compiler logs and a selected
exact runner excerpt. Complete decoded runner logs were read through cleanup;
the excerpt is not a full raw runner archive. No absent receipt is fabricated.
Raw packet tree469b1956e46adfa05086fa2c3956fb5090da72c0 and raw verified tree
114f60c5040ba5741335570e8e370adb60a8c9b8 match independent local Git hashing.
Handoff: research/TARGET_DETERMINING_ROW_BUDGET_HANDOFF.md. Keep this PR draft.
