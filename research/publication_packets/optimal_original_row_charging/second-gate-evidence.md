# Second gate: capacitated Hall equivalence clean; one empty-membership repair remains

PR #343 is OPEN/DRAFT and unmerged. Target:
Hirsch.optimal_original_row_edge_charging.
Tested repaired proof: a59329c6d365be307e73b11ea42122019593ef91.
Source: 356 lines / 14566 bytes, blob1344d0a53a5dd6b45d5c08583a1a9b856dbb382d,
SHA2561f062f05c02f14cd713d64e3cfa467758b4d85f2bd7fd4e9e8be21acb569bdb9.
Main at gate: b59bda5572a09cdfba2ebac74a6cb275281136c7.

## Actual second gate

Coordination5814634450; NEW top-level request5814676979;
acknowledgement5814680629; run36003244581. These were actually posted and read
back. Gate107644798704 succeeded. Verifier107644876259 restored the exact pinned
environment, then driver compilation failed at282:14 with one displayed error:
Unknown constant Finset.not_mem_empty. Standalone solution and exact target
statement were not reached. Publish107645432213 and report-verify107645431516
were skipped. No verified artifact or publisher receipt was produced.

This was the SECOND hosted compiler attempt, with exactly one new trigger this
continuation. There have been zero theorem registrations or actual platform
proof submissions, and no theorem/submission ID, ACCEPTED or authenticated
Proved result. No second trigger or post-gate publication-input edit followed
this failure. The first run35998089588 remains preserved, not rewritten as success.

## What the applied repair accomplished

The exact saved three-area patch was applied:28 added lines/17 removed. It fixes
product notation, the initial empty-set proof entry, and the public let/filter/
load conversions. All declaration statements, public type, accepted helpers,
problem.json and explanation.md stayed unchanged. The public proof body changed
as specified by that proposal. The remote source matched the saved candidate.

The transitive reports for exposed_edge_row, forced_le and NOW capacity_iff
contain only propext, Classical.choice and Quot.sound. In particular the generic
capacitated Hall equivalence has a clean independent report:

    Capacity S k iff every J subset I has |{t : S_t subset J}| <= k*|J|.

Both directions are covered: any assignment implies the forced-row inequalities,
and those inequalities yield an injective row-slot assignment and a row load
bounded by k. This is stronger than the earlier clean necessary counting lemma.
The helper applies to arbitrary finite eligible sets contained in I; no small
capacity or matching is supplied as a premise.

The optimum and public solution reports still include failed-elaboration
sorryAx. No admission was written. The passing Hall helper does not establish
full-packet verification or a Prove2Me verdict.

## Exact one-line next proposal: UNAPPLIED and UNCOMPILED

In the empty-J contradiction, after rewriting hJE, hiJ already asserts i in the
empty finite set. Replace line282:

    exact Finset.not_mem_empty i hiJ

with:

    simpa using hiJ

This uses empty-membership simplification rather than another guessed lemma
name. It adds one line/removes one, with all declaration statements, the ENTIRE
public root statement and proof, accepted helpers and metadata unchanged.
Proposed source:356 lines/14549 bytes, computed blob
87d719f1cde8a87c29a90cfd7d6bfec4801ce7e7, SHA256
d3228b6e74e04152953b153a5859a02b24d16bb4a7054ba874bc340133a03c76.
Patch application/reversal succeeds; this is not Lean compilation. The proposal
is not applied to the publication source. Further errors may appear.

Patch: research/verification/optimal-original-row-charging/second-attempt/
proposed-empty-membership-repair.patch. Resume THIS PR after live ownership and
pending-request checks, using local compilation where available and one prepared
complete pinned gate. Do not rename the target or weaken its public assumptions.

## Mathematical scope and remaining route obligation

The full candidate derives an optimal integral assignment of ORIGINAL row labels
for a GIVEN finite family of genuine original exposed edges avoiding the target.
Eligible labels are derived from actual target slack and endpoint tightness.
For each capacity smaller than the derived optimum K, it produces a nonempty
row subset whose forced edge occurrences exceed its capacity. K and its witnesses
are conclusions, not favorable-load hypotheses, but the complete optimum proof
still requires the local correction above.

Actual target/endpoints, their extremality and whole nondegenerate original
exposed segments remain inputs. Occurrences may repeat; the finite H-body may
be unbounded and the ambient dimension is arbitrary. No polynomial bound on K,
route construction, shortestness or Polynomial Hirsch result is asserted. The
next geometric obligation remains controlling forced-row density along a
constructed ORIGINAL-edge route, not optimizing labels on an arbitrary detour.
A terminal target-incident edge is excluded from this charging scheme.

## Fresh execution and durable evidence

Both unchanged standalone rational suites ran in this continuation. All FOUR
complete report/fixture files reproduced their prior bytes. The exhaustive
2928 eligible-set families/22968 assignments agree;67 geometric ledgers contain
1269 original-edge occurrences, with nine rejected controls. The64D short route
retains the greedy63-to-optimal1 improvement. The8D Gray detour still forces32
although its endpoints are adjacent; that is not a diameter lower bound.
Python, JSON and the flow/geometry implementation are not kernel-verified.

Only request artifact10808773432 exists:315 bytes, SHA256
4989a459b62297f17fb19042a727a556c6678c3d1649e2ecf61dc5ff8506eecf.
Its downloaded ZIP was rehashed; the exact resolved request is preserved. The
complete decoded verifier log was read through cleanup. The saved complete
compiler block includes warnings, the one error and all five reports without
timestamps; setup/cache/cleanup are omitted. It is not a full raw runner archive.
No unavailable verified packet, receipt or platform API body is invented.

The second-attempt directory preserves the tested inputs, prior handoff,
diagnostics/reports, raw request, proposed patch and labelled source/test/run
readbacks. The download also contains both original request ZIPs, first-failure
history, complete fresh outputs, the unchanged runnable script and full uncompiled
next proposal. Local Lean/Lake/Elan and checked conventional caches were absent;
toolchain DNS failed. Source checks and rational tests are not compilation.
Keep Lean4.30.0/Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.9,
other owners, accepted inputs and verifier/publisher safeguards unchanged.
