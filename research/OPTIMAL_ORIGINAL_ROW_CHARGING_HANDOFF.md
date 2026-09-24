# PR343: Hall equivalence verified; one empty-membership goal remains

Read live main, current instructions, PR comments and ownership before continuing.
Resume this SAME target. Respect other owners, including #326/#282/reserved #210.
The older first-gate handoff is history: its saved repair has already been applied.

Branch: proof/optimal-original-row-charging.
Packet: research/publication_packets/optimal_original_row_charging.
Target: Hirsch.optimal_original_row_edge_charging.
Tested repaired proof:a59329c6d365be307e73b11ea42122019593ef91.
Source356 lines/14566 bytes, blob1344d0a53a5dd6b45d5c08583a1a9b856dbb382d,
SHA2561f062f05c02f14cd713d64e3cfa467758b4d85f2bd7fd4e9e8be21acb569bdb9.
Main at gate:b59bda5572a09cdfba2ebac74a6cb275281136c7.

## Actual verification and publication state

Coordination5814634450; request5814676979; acknowledgement5814680629;
run36003244581. Gate107644798704 passed; verify107644876259 failed driver
compilation at282:14: Unknown constant Finset.not_mem_empty. Standalone solution
and exact statement not reached; publish107645432213/report107645431516 skipped.
Second hosted attempt; only one trigger this continuation. Zero registrations
or actual proof submissions, no IDs/receipt/ACCEPTED/Proved. No full packet pass.

The exact28-addition/17-deletion saved repair resolved the earlier errors.
The capacity_iff report is NOW standard-only, alongside exposed_edge_row and
forced_le. Both directions of the finite capacitated Hall criterion are clean.
optimum and public solution retain failed-elaboration sorryAx; no admission was
written. No additional gate or post-gate source/metadata edit was made.

## Exact next proof action

Apply second-attempt/proposed-empty-membership-repair.patch. It replaces only:

    exact Finset.not_mem_empty i hiJ

with:

    simpa using hiJ

Here hiJ is already membership in the empty Finset after rewriting hJE. The
proposal adds one line/removes one. All signatures, public root statement AND
proof, accepted helpers, metadata and explanation remain unchanged.
Proposed356 lines/14549 bytes, computed blob
87d719f1cde8a87c29a90cfd7d6bfec4801ce7e7, SHA256
d3228b6e74e04152953b153a5859a02b24d16bb4a7054ba874bc340133a03c76.
It is UNAPPLIED to publication source and UNCOMPILED. Exact patch roundtrip
passed, not Lean. Further compiler errors may appear. Recheck live ownership,
apply deliberately, compile locally where possible and use one complete prepared
gate on this same PR. Do not reapply the older product/public-filter patch.

## Scope and meaningful next mathematics

The complete candidate optimizes original-row labels for an INPUT finite family
of genuine non-target original exposed edges, deriving all eligibility and an
optimal load with forced-row overload witnesses. It does not construct a route
or prove polynomial congestion. Repeated occurrences, unbounded bodies and
arbitrary dimension remain allowed; actual endpoints/target and whole original
exposed edges are explicit. The remaining conjecture-facing obligation is to
control forced-row density along a constructed original ordinary-edge route.

## Evidence and reproduction

Current packet note:second-gate-evidence.md.
Evidence:research/verification/optimal-original-row-charging/second-attempt/.
First-attempt evidence is unchanged; previous-handoff.md preserves the old state.
Only new artifact10808773432 exists (315 bytes,SHA256
4989a459b62297f17fb19042a727a556c6678c3d1649e2ecf61dc5ff8506eecf).
The original request ZIP and complete fixtures are in the export. Diagnostics
are the full displayed compiler block, not a full raw runner archive.

    python3 scripts/test_optimal_row_charging.py --out /tmp/charging-small
    python3 scripts/test_optimal_row_charging.py --large --out /tmp/charging-large

Both unchanged suites reran; all four complete outputs reproduced prior bytes.
2928 set families/22968 assignments,67 ledgers/1269 occurrences and9 rejected
controls remain. Selected64D routes are not complete graphs; the Gray detour's
unavoidable load is not a diameter lower bound. Python/JSON are not kernel-verified.
No retry or alternate upload of the unrelated blocked script was attempted.

Local compiler/cache unavailable; toolchain DNS failed. Preserve Lean4.30.0,
Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f, reviewed strict0.10.9,
accepted inputs, duplicate guards and secret-free verifier/trusted publisher.
