# PR #304: six-row tiny actual gains — compiler-blocked draft

Read current STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH, live PR heads,
comments and receipts before continuing. This continuation started from
main d6e667d1d2ffa4eaa012e941fadec2898b6f9c5c. Coordination comment5734235752
on accepted #303 was posted and read back. #300 separated-pair routes and #302
even-gap catalogue remain their owners' work. Reserved #210 is untouched.

## Actual gate and last observed outcome

A NEW top-level conversation comment5734429736 on open same-repository #304
began `/prove2me publish research/publication_packets/moment_six_row_small_gain`.
Acknowledgement5734431801 resolved prooff84d79808cf6fafab2e02027d5f0af81446f223a
and run35380332439. Gate105714718592 succeeded; verify105714762470 FAILED
driver compilation at18:30:13Z on2026-09-18. Publish105715440435 and report-
verify105715440440 were skipped. No theorem registration/submission, verified
packet, authenticated ACCEPTED verdict or live Proved readback was obtained.
Exactly ONE hosted gate was triggered. Keep this PR OPEN/DRAFT; do not merge.

The raw resolved request was downloaded in artifact10562007847, hash
 eb8e78e7bf47d8eb3c3e9c2f0a56c64965f08886a33eb066ffeba8985d403ba8.
The original ZIP is in the export; resolved.json is committed. The full job log
was inspected. first-diagnostics.txt preserves selected EXACT excerpts with
explicit omissions; it is not mislabeled as the full raw log. first-gate.json
is a separately labelled derived failure summary. No unavailable receipt is
fabricated and no fresh mission-root/leaf platform poll is claimed.

## Formal blocker — not a one-line repair

Actual diagnostics concern finite-index/vec notation reduction, multi-location
simplification after a goal closed, finite-set cardinality/intersection facts,
a reordered nonzero denominator, and route point index inference. The original
line groups are582/585/607/610,595,635/711/712/720/730/850/852/854,
691/790/793 and846. All FIVE printed new declarations contain sorryAx; the
failed nodes_injective name is also propagated. Those are FAILED elaboration
reports, not a passing audit or a permitted new axiom.

The complete908-line source is preserved unchanged at blob
8e23165c5e8d06b15d8b81c7153defc38b9426bf, SHA256
0c895c669d3a113d135b38e458826e16500a68acd2b28c9685f4f3a9b6051cfe.
No proof or metadata edits and no second trigger followed the failure. The
local repair plan gives concrete implementation directions but is NOT a tested
patch. It requires actual pinned local compilation; correcting these errors
may expose further ones. Local Lean/Lake is unavailable and toolchain-host DNS
failed. Arithmetic/source checks are not a substitute.

## Written mathematical progress

For a=(-1,0,e,2e,3e,1),0<e<1/4, use the ORIGINAL 2D mean-centered moment rows.
The five explicit points u,l,r,v,b have exact tight sets{2,3},{1,2},{3,4},
{0,5},{0,1}. The note writes every original slack and proves its sign. Accepted
moment geometry then gives genuine vertices and the exposed edges u-l,u-r,
l-b,b-v. A source-cone/exposing-functional argument excludes ALL other incident
exposed-segment neighbors; it does not assume an adjacency table.

For target score f=A_0+A_5, the two actual gain fractions are

    2e^2/(1+2e^2),
    2e^2(1-2e^2)/((1+2e^2)(1+10e^2)).

Both are positive and below2e^2. Choosing e=min(1/8,delta/4) makes them below
ANY requested positive delta. Yet u,l,b,v remains a THREE-original-edge route.
This goes beyond #303's written mass example, where the best actual gain stayed
near6/13: here the true best incident gain tends tozero at fixed dimension and
row count. Related earlier written contraction obstructions in #256 are credited;
no historically new general obstruction is claimed.

The written argument is complete as ordinary mathematics but the Lean packet is
NOT yet verified. This is not a diameter lower bound, a long trajectory or
Polynomial Hirsch. Formal shortestness, multi-step stalling and behavior for
arbitrary objectives are not conclusions. Use the short route to avoid falsely
inferring a long graph path from a small first-step score gain.

## Accepted reuse, tests and exact scope

The full544-line accepted namespace prefix through Hirsch.MomentEdges is
byte-identical to #303's verified source; all five dependency manifest hashes
were recomputed. Old public targets are omitted and not resubmitted. The new
public statement uses explicit Mathlib lets and import/open/options-only
preamble, with no feasible point, neighbor/rank/edge or route oracle.

The Fraction-only test independently reconstructs59 complete graphs from885
original square systems:354 vertices/354 edges in total,1770 original point-row
checks,59 source-neighbor classifications and177 route edges. Eight delta
choices include2^-128. All59 saved records audit with explicit-point, solver
and graph discovery disabled; five forgeries fail. Every computed shortest
distance is3, but the public target asserts only the explicit three-edge route.

The one-script clean replay matches both the full3548-byte report and31652-byte
fixture. Report05114a9296c14bd680d1c14279c4cad0262789a9c861e152d6ba053bfd81a2b7;
fixturef72f0b9698aa24f254ce0af05cb4f2fed97dffa1c370106015c08ce514a7ea44.
Script blobff17e71b2022297e9df63429b3ca8481a132af72, SHA256
0a6ad3919ad7cedd49afcdcc3e1692d8577e22f7e1d0e2e52c2a09a0433e70a2.
The full fixture and original request ZIP accompany the export and regenerate:

    python3 scripts/test_moment_six_row_small_gain.py --out /tmp/six-row-check

Current original proof/metadata, root STATUS, Lean/Mathlib pin, protocol0.10.4,
workflows, allowlist, duplicate safeguards and trusted verify/publish credential
split remain unchanged. The next formal task is local reduction/assembly repair
of THIS existing packet, not a duplicate theorem or broad new decomposition.
The conjecture still requires coefficient-independent control of actual edge
routes; this work excludes one proposed local numerical shortcut rather than
supplying that global bound.
