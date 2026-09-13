# Resume the Polynomial Hirsch project in a new chat

Read STATUS.md, AGENTS.md, CLOUD_AGENT.md and SKILL.md, then live open PRs and
their comments. This guide supplements those files; it does not freeze their
state. Another agent was handling #210 when this guide was written. Do not
modify or trigger that work without an explicit reassignment.

## Accepted compact-dual result (#216)

Packet: `research/publication_packets/compact_dual_minkowski/`.
Theorem `Hirsch.compact_dual_minkowski_erosion`:
`a6e2a38d-00e3-46d6-b232-7cddee5e30e1`.
Submission `2976ce68-c33c-4cab-b48e-8a7f46be211a`: ACCEPTED, live Proved.
Proof head `115b3ede788bca52bcac568d1aa05e62a0d92559`.
Run https://github.com/jjoshua2/prove2me-work/actions/runs/34776731744
Evidence: packet/accepted-evidence.md. Do not resubmit it.
This proves compact-convex whole-set sufficiency from all weighted tests.

## Accepted algebraic finite-circuit result (#218)

Packet: `research/publication_packets/finite_positive_circuit_tests/`.
Theorem `Hirsch.finite_positive_circuit_dual_tests`:
`8f3c4cc7-be73-4ecf-9e17-816c710e20d7`.
Submission `3fd7936c-8271-4a24-b342-d60bfd29529f`: ACCEPTED, live Proved.
Proof head `ad4345bb17066c91b13d09ab0c8e757cbc5b65c9`.
Run https://github.com/jjoshua2/prove2me-work/actions/runs/34778403314
Evidence: packet/accepted-evidence.md. Do not resubmit it.
One fixed support-indexed positive-circuit family detects every linear test on
the nonnegative kernel. Negative-certificate reduction and ray uniqueness are
proved, not assumed. Its original 242-line proof passed unchanged.

## Accepted finite allocation/Minkowski result (#219)

Packet: `research/publication_packets/finite_allocation_minkowski/`.
Theorem `Hirsch.finite_allocation_minkowski_criterion`:
`09c33216-ba2f-4c9f-b75e-e9d8279e8358`.
Submission `f5304244-5800-46f7-b0c5-98cdf4c6d71a`: ACCEPTED, live Proved.
Proof head `9d3aea2f4120f44a6c43b882d79c9f6f7fcb00c6`.
Run https://github.com/jjoshua2/prove2me-work/actions/runs/34781016108
Evidence: packet/accepted-evidence.md, publication-receipt.json,
packet-audit.json and artifact-readback.json. Do not resubmit it.

This composes #216/#218 with a proved bounded-simplex alternative. It concludes
one actual allocation and whole-set Minkowski equality from the fixed finite
tests. Original-polyhedron boundedness, generator independence, a Farkas axiom,
and a pre-existing feasible allocation are not assumed. The first hosted run
failed at four elaboration sites; exactly those proof lines were repaired,
with all statements unchanged. The final solution, driver and statement compile
and the transitive audit allows only propext, Classical.choice and Quot.sound.
This history is preserved in research/FINITE_ALLOCATION_FIRST_GATE.json.

The next exact targets are described in research/FINITE_CIRCUIT_ALLOCATION_NEXT.md:
original-H primal/dual support optimality to eliminate the remaining universal x,
and the separate rank-plus-one support bound plus executable enumerator mapping.
FINITE_CIRCUIT_RANK_NEXT.md gives a mathematical injectivity proof to formalize.
Inspect newer work before choosing either obligation. None of these accepted
results proves Polynomial Hirsch or supplies arbitrary residual edge routes.

## Commands are real, new, top-level PR comments

On an OPEN SAME-REPOSITORY PR, post as jjoshua2. The command must start the
comment, without a code fence, quotation or preceding explanation. Editing an
old comment or posting an inline review comment is not the intended trigger.

Module-only build, no packet or publication:

    /prove2me verify --targets Solutions.SomeModule

Packet compilation and axiom audit, no publication:

    /prove2me verify research/publication_packets/PACKET

Packet compilation/audit, frozen artifact, then publication and polling:

    /prove2me publish research/publication_packets/PACKET

--targets Module.Name can accompany a packet command for extra Lake builds;
it never replaces the packet for publication. The current connector action is
GitHub.add_comment_to_issue(repo_full_name=..., pr_number=..., comment=...).
Discover the available schema and invoke it; displaying a command in chat does
not post it. No workflow_dispatch or extra token is required.

## Follow the evidence, not a stale handoff snapshot

Read the command comment back, then the bot acknowledgement for the exact run ID
and resolved proof SHA. The issue_comment workflow executes from main; its own
head SHA may differ from the candidate proof SHA. Use the frozen request and
manifest. Commit-workflow lookups can filter out issue_comment runs: use the
run ID from the bot comment. Before a final status report, inspect the latest
relevant comments/jobs and distinguish historical evidence from a fresh poll.
A local-only draft in an older chat is not evidence that no newer PR has closed
its mathematical obligation, or that the old and new source bytes are identical.

Inspect jobs, logs and artifacts. Compilation, axiom audit and authenticated
Prove2Me acceptance are distinct. Claim Proved only after the trusted publisher
reports acceptance and live readback. Preserve theorem/submission IDs, source
hashes and artifacts before retention expiry. Label derived summaries as such;
do not invent raw platform responses. Do not resubmit accepted or pending work.
If a run is unfinished at the end of the turn, report its last observed state
without promising background monitoring.

The verify job has no Prove2Me secret. Only trusted main code in a separate
publish job uses PROVE2ME_API_KEY. Never request, paste or commit that key, or
change the security split to work around a tool block. A blocked action is not
evidence of a workflow defect; preserve the handoff without attempting a bypass.

## Proof preparation

A publishable packet has solution.lean, problem.json and explanation.md. Use a
top-level theorem solution with exactly the target type; never import the
target as its own proof. Avoid local def/structure declarations in the statement
preamble: separate compilation does not guarantee platform type identity.
Keep the committed Lean/Mathlib pin. Iterate locally when Lean is available,
then use a prepared final gate rather than speculative hosted compile loops.
If no local compiler is available, state that limitation; text and Python tests
are not Lean compilation. Preserve failed-gate diagnostics and never convert a
failed or merely queued run into an acceptance claim.

## Paste into a new chat

@GitHub Continue the Polynomial Hirsch project in jjoshua2/prove2me-work. Read
STATUS.md, AGENTS.md, CLOUD_AGENT.md, SKILL.md and CONTINUE_HIRSCH.md; inspect the
live open PRs, exact heads, comments and verification/publication receipts before
choosing work. Another agent is handling #210: leave it unchanged and untriggered
unless I explicitly reassign it. Continue a concrete unowned proof obligation,
reuse accepted results and avoid duplicate decompositions or submissions.

#216, #218 and #219 are ACCEPTED; do not resubmit their packets. Read
research/FINITE_CIRCUIT_ALLOCATION_NEXT.md and check whether newer work has
closed or claimed its remaining support-optimality, rank-bound or executable
catalogue obligations. Preserve all assumptions and the Lean/Mathlib pin.
Compile locally where available; do not label Python tests as Lean verification.

When a complete packet is ready on an open same-repo PR, actually post a NEW
TOP-LEVEL PR CONVERSATION COMMENT with first line:
/prove2me publish research/publication_packets/PACKET
For compile-only work use /prove2me verify --targets Solutions.ModuleName or
/prove2me verify with an explicit packet path. Do not merely print the command,
request workflow_dispatch, ask for a secret or weaken security. Read back the
comment and follow the bot's exact SHA/run through jobs, logs, artifacts and
the authenticated verdict. Do not duplicate pending work. Preserve evidence,
update the handoff and report the actual result and remaining hypotheses.
