# Resume the Polynomial Hirsch project in a new chat

Read STATUS.md, AGENTS.md, CLOUD_AGENT.md and SKILL.md, then live open PRs and
their comments. This guide supplements those files; it does not freeze their
state. Another agent was handling #210 when this guide was written. Do not
modify or trigger that work without an explicit reassignment.

## Completed reference example

PR #216's `research/publication_packets/compact_dual_minkowski/` was compiled,
axiom-audited and ACCEPTED by Prove2Me at proof head
`115b3ede788bca52bcac568d1aa05e62a0d92559`.

Theorem `Hirsch.compact_dual_minkowski_erosion`:
`a6e2a38d-00e3-46d6-b232-7cddee5e30e1`.
Submission `2976ce68-c33c-4cab-b48e-8a7f46be211a`; live status `Proved`.
Run: https://github.com/jjoshua2/prove2me-work/actions/runs/34776731744
Evidence: `research/publication_packets/compact_dual_minkowski/accepted-evidence.md`.
Do not resubmit it. It is a compact-convex whole-set sufficiency lemma, not a
proof of Polynomial Hirsch.

## Accepted algebraic finite-circuit continuation (#218)

`research/publication_packets/finite_positive_circuit_tests/` is also ACCEPTED,
with authenticated live Proved status. Its 242-line direct proof compiled and
passed the axiom audit unchanged on the first prepared hosted gate.

Theorem `Hirsch.finite_positive_circuit_dual_tests`:
`8f3c4cc7-be73-4ecf-9e17-816c710e20d7`.
Submission: `3fd7936c-8271-4a24-b342-d60bfd29529f`.
Proof SHA: `ad4345bb17066c91b13d09ab0c8e757cbc5b65c9`.
Run: https://github.com/jjoshua2/prove2me-work/actions/runs/34778403314
Evidence: `research/publication_packets/finite_positive_circuit_tests/accepted-evidence.md`.
Handoff: `research/FINITE_POSITIVE_CIRCUIT_HANDOFF_2026-09-13.md`.

One fixed support-indexed positive-circuit family detects every linear test on
the nonnegative kernel. The negative-certificate support reduction and
positive-ray uniqueness are proved, not assumed. Do not resubmit this packet.
The sharper rank+1 support bound, executable enumeration, and whole geometric
allocation adapter remain separate. `research/FINITE_CIRCUIT_ALLOCATION_NEXT.md`
states the exact allocation matrix and next sufficiency target. Inspect newer
work before choosing that obligation. No Polynomial Hirsch proof is claimed.

## Commands are real, new, top-level PR comments

On an OPEN SAME-REPOSITORY PR, post as `jjoshua2`. The command must start the
comment, without a code fence, quotation or preceding explanation. Editing an
old comment or posting an inline review comment is not the intended trigger.

Module-only build, no packet or publication:

    /prove2me verify --targets Solutions.SomeModule

Packet compilation and axiom audit, no publication:

    /prove2me verify research/publication_packets/PACKET

Packet compilation/audit, frozen artifact, then publication and polling:

    /prove2me publish research/publication_packets/PACKET

`--targets Module.Name` can accompany a packet command for extra Lake builds;
it never replaces the packet for publication. The current connector action is
`GitHub.add_comment_to_issue(repo_full_name=..., pr_number=..., comment=...)`.
Discover the available schema and invoke it; displaying the command in chat
alone does not post it. No workflow_dispatch or extra token is required.

## Follow the evidence

Read the comment back, then the bot's queued acknowledgement for the run ID and
resolved proof SHA. The issue_comment workflow itself runs from main, so its
own head SHA may differ from the candidate proof SHA. Use the resolved request
and frozen manifest. A commit-workflow lookup may filter out issue_comment
runs; use the run ID in the bot comment instead.

Inspect jobs, logs and artifacts. Compilation, axiom audit, and authenticated
Prove2Me acceptance are different outcomes. Claim Proved only after the trusted
publisher reports acceptance and live readback; preserve theorem/submission IDs
and source hashes. Download artifacts before retention expiry. Do not blindly
resubmit a pending job. If a run is unfinished at the end of the turn, report
the last observed state without promising background monitoring.

The verify job has no Prove2Me secret. Only trusted main code in a separate
publish job uses PROVE2ME_API_KEY. Never request, paste or commit that key, or
change the security split to work around a tool block. A blocked action is not
evidence of a workflow defect; report it and preserve the handoff, without
attempting a bypass.

## Proof preparation

A publishable packet has solution.lean, problem.json and explanation.md. Use a
top-level `theorem solution` with exactly the target type; do not import the
target as its own proof. Avoid local def/structure declarations in the statement
preamble because separate compilation is not enough to guarantee platform type
identity. Keep the committed Lean/Mathlib pin. Iterate locally when Lean is
available, then use one prepared final gate rather than speculative hosted
compile loops. If this environment lacks a compiler, report that limitation;
text checks and Python tests are not Lean compilation.

## Paste into a new chat

@GitHub Continue the Polynomial Hirsch project in jjoshua2/prove2me-work. Read
STATUS.md, AGENTS.md, CLOUD_AGENT.md, SKILL.md and CONTINUE_HIRSCH.md; inspect the
live open PRs, exact heads, comments and existing verification/publication
receipts before choosing work. Another agent is handling #210: leave it alone
unless I explicitly reassign it. Continue a concrete unowned proof obligation,
reuse accepted results and avoid duplicate decompositions or submissions.

The compact_dual_minkowski packet from #216 and finite_positive_circuit_tests
packet from #218 are ACCEPTED; do not resubmit either. Work toward the exact
allocation adapter in FINITE_CIRCUIT_ALLOCATION_NEXT.md or the actual newer
frontier. Preserve assumptions and the Lean/Mathlib pin; compile locally where
available.

When a complete packet is ready on an open same-repo PR, actually post a NEW
top-level PR comment with first line:
/prove2me publish research/publication_packets/PACKET
For compile-only work use /prove2me verify --targets Solutions.ModuleName or
/prove2me verify with an explicit packet path. Do not merely print the command
in chat, request workflow_dispatch, ask for a secret, or weaken security. Read
back the comment and follow the bot's exact SHA/run ID through jobs, logs,
artifacts and the authenticated verdict. Avoid duplicating pending work.
Preserve receipts and update the handoff. Report mathematical progress,
remaining hypotheses and actual status, without promising work after the turn.
