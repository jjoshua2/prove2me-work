# Resume the Polynomial Hirsch project in a new chat

Read STATUS.md, AGENTS.md, CLOUD_AGENT.md and SKILL.md, then live open PRs and
their comments. This guide supplements those files; it does not freeze their
state. Check current ownership and the user's latest assignments. #210 was
previously reserved to another agent; subsequent user permission may allow
cross-branch work, but avoid conflicting edits and duplicate publication runs.

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

## Later accepted bridges: support, rank and normalized vertices

#221 supplies accepted original-H support optimality; #222 supplies the accepted
positive-circuit signed-kernel/rank-plus-one theorem. Do not treat their earlier
next-step notes as evidence that these results remain unproved. Inspect their
current packets and authenticated receipts before using exact interfaces.
#227 is the separate allocation/support-budget composition line; inspect its
latest state and ownership rather than starting a duplicate.

#224's `Hirsch.normalized_positive_circuits_iff_extreme_points` is ACCEPTED and
merged. Theorem56d0cf40-7b2f-49cb-98c5-fe6a074637d5, submission
9367eda0-1710-493c-b2f7-19458fba31ed, run34784148514. The safe resume reused its
existing registration and compiled the same proof; it was not a duplicate
problem registration. Evidence is in
`research/publication_packets/normalized_circuit_vertices/accepted-evidence.md`.
These are vertices of the auxiliary normalized kernel section, not vertices
of the original polytope. Do not resubmit #224.

## Accepted executable catalogue checker (#229)

Packet: `research/publication_packets/checked_circuit_catalogue/`.
Theorem `Hirsch.checked_rational_circuit_catalogue_exact`:
49468d71-eb2e-4908-a15e-a89d1d23622a.
Submission0dcf5eea-df74-4295-9a5e-c71edb96589d: ACCEPTED, authenticated live Proved.
Proof head1f13787356e7aee48c2fa6e026915f2d4c0805b2, run34785744936.
Merged in12a9e193d92de2c31eedba6870f1df0722c37931. Proof and original metadata
are unchanged after the successful gate; exact receipts and artifact hashes
are committed in the packet. Three concrete examples passed by decide +kernel.

For rational k-by-n A, every support up to size k+1 supplies either an exact
left inverse of [A_S;ones], or a nonzero supported zero-mass null vector.
The finite Boolean audit plus output filter is proved to return EXACTLY all
normalized REAL positive circuits. This certifies omitted supports as well as
valid emitted rays, without trusting RREF or a rank/enumeration oracle.
Both Python producer/auditor scripts and executed tests are committed. Python
and JSON decoding are not Lean-extracted; concrete data must pass the Lean
checker for a kernel-certified instance. The large tables were tested in
Python, not silently treated as individually kernel-evaluated.

The next connected formal task is to compose this ACTUAL checked finite
catalogue with the accepted allocation and exact-support-budget criteria,
including casts and normalized circuit representatives. See the packet's
accepted-evidence.md and research/CHECKED_CATALOGUE_ALLOCATION_EXAMPLE.md.
The example recovers the known joint triangle/square budget through18 audited
circuits; it is an exact numerical integration test, not the formal composition.
Do not reprove catalogue completeness or republish #229. Useful universal shape
selection and arbitrary residual ordinary-edge routing remain mathematical
obstacles. None of these results proves Polynomial Hirsch.

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
without promising background monitoring. For asynchronous registration, preserve
and resume the exact existing job via the trusted workflow; never create a
second theorem merely because a prior run returned PUBLISH_PENDING.

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
choosing work. Respect the current agents' assignments and my latest permission
about cross-branch work. Continue a concrete unowned proof obligation, reuse
accepted results and avoid duplicate decompositions or submissions.

#216/#218/#219/#221/#222/#224/#229 have accepted results; do not resubmit their
packets. Inspect #227 and newer work before composing the executable checked
catalogue from #229 with exact allocation/support budgets. Do not mistake
historical handoffs for the current frontier. Preserve assumptions and the
Lean/Mathlib pin; compile locally where available. Python tests are not Lean
verification and generic checker acceptance does not certify arbitrary JSON.

When a complete packet is ready on an open same-repo PR, actually post a NEW
TOP-LEVEL PR CONVERSATION COMMENT with first line:
/prove2me publish research/publication_packets/PACKET
For compile-only work use /prove2me verify --targets Solutions.ModuleName or
/prove2me verify with an explicit packet path. Do not merely print the command,
request workflow_dispatch, ask for a secret or weaken security. Read back the
comment and follow the bot's exact SHA/run through jobs, logs, artifacts and
the authenticated verdict. Do not duplicate pending work. Preserve evidence,
update the handoff and report the actual result and remaining hypotheses.
