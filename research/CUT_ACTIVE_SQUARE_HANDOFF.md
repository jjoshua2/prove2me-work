# PR #294: selected active square system — ACCEPTED

## Current state and exact proof

Hirsch.cut_vertex_selected_active_square_system is ACCEPTED. The trusted
publisher receipt records live Proved. Do not resubmit this packet.

Theorem: d01a7a03-fda5-4dd3-a058-7f38127c3228.
Submission: 6f3c3e48-8375-4dbd-a965-c296859574e8.
Accepted proof: 053cc6ac62a489b6d104968f72a2c1e8e1b9c4b4.
Run: 35266694176; trigger5720225598; resolved5720227881; verdict5720271472.
Trusted workflow main: baa437ee2241fedb32028f9ac140c7770036ec0c.

Read the packet's accepted-evidence.md, raw publication-receipt.json and
packet-audit.json. All three compilation modes exited zero. All six transitive
axiom reports contain only propext, Classical.choice and Quot.sound. Final
jobs gate/verify/publish succeeded; report-verify was skipped. Live Proved is
the trusted publisher's authenticated readback, not a separate direct chat poll.

## What is now proved

For any actual extreme point x of convexHull(S) intersected with finitely many
original linear halfspaces, construct a strictly positive affinely independent
support of n points in S, n<=d+1, and a finite set J of cuts actually active at x.
The construction retains the mass equation and has |J|+1=n. For EVERY real
mass and EVERY real vector of selected values, the square system has exactly
one real weight vector. Mass one and the selected original right sides recover
the actual positive weights, even among signed alternatives.

Neither the support, weights, row set, inverse, determinant nor rank certificate
is a caller premise. Selected rows are ORIGINAL active indices, not arbitrary
linear combinations. S may be infinite or noncompact; selected support points
may individually violate the added cuts. A singleton support selects no cuts.
Arbitrary prescribed values are not claimed to give positive weights or a
feasible barycentre. The support or selected row set need not be unique.

The complete accepted #291 source is reused, with only its public root/print
name changed to accepted_positive_support. The new helper is
Hirsch.SelectedActiveRows.mass_preserving_square. It starts basis extension
with the nonzero mass row. The selected rows are independent; any vector
annihilating them annihilates their span and every active row. The accepted
active-image independence makes the coefficient kernel zero. Opposite dimension
inequalities force |J|+1=n, and equal dimensions give surjectivity and uniqueness.
This is classical existence, not a Lean-extracted executable greedy selector.

## Actual attempt history — do not erase the two failures

Previous runs35249408324 and35249850308 failed driver compilation before any
registration/submission. Their exact source snapshots, requests and diagnostic
excerpts remain in verification/cut-active-square/. The first applied repair
normalized RingHom.id; the remaining failure was the bundled linear-map
application to the constant-one mass row.

This continuation applied ONLY the already preserved proposed-local-repair.patch:
explicitly change that application to sum_i u_i*1=0, then simplify mul_one.
Every theorem type, hypothesis, bound, problem.json, explanation.md and accepted
dependency remained unchanged. The 506-line repaired source passed the third
lifetime compiler gate and FIRST actual platform submission. Exactly ONE new
publish command was used in this continuation, with no subsequent proof edits
or trigger loop. No local Lean/Lake was available; this is pinned hosted evidence.

The former blocked handoff is preserved verbatim as resume/pre-resume-handoff.md
and at commit27df38b482cd54841e1ef94642e081da8a2e2df1. Old submission-state.json
and source-manifest.json in the parent verification directory are HISTORICAL
failed-attempt records, superseded for current status by resume/publication-readback.json.
The old proposed patch is retained as history; it is now applied and verified.
No successful receipt has been substituted into the earlier failed runs.

## Immutable evidence and supporting checks

Accepted source blob04ac0dda22a4ff0776d11f90885391aaacd5dfc7,
SHA2564071a0a4b03f17e7704078b1e9c3fda81f936fa6a6e504cfa24734a906a2a15f.
All five frozen file hashes and all three new original ZIP digests were checked.
Raw manifest/audit, driver/solution/statement, complete compile logs, request,
verified-artifact summary, publication receipt and exact publisher comment are
preserved. Derived inspection records are separately labeled. The target stub's
by sorry is not part of the admission-free solution. Raw individual platform
API response bodies are not exported by the publisher and are not fabricated.

The unchanged Fraction test was rerun:96 row systems,288 signed recoveries,
2448 inverse identities and1332 small candidate row subsets. Seven simplex-cut
vertices through dimension16 include74 original active rows and redundant cuts.
Five adverse controls include a mathematical missing-mass rank example, not five
claimed parser rejections. Four stored in-memory inverse records audit with
selection/elimination/inverse discovery disabled. The full rerun report is
byte-identical to the prior clean replay. These checks are not Lean-extracted.

    python3 scripts/test_cut_active_square.py --out /tmp/cut-active-square-tests.json

## Next work and ownership

The support-selection and active-row extraction interfaces are now formally
closed. Do not open another child assuming or reproving the same row basis.
A separate agent has claimed finite catalogue composition in #294 comment
5720255040. Its proposed first version uses all active masks and a 2^m factor.
This accepted J interface may support a sharper later recipe count, but that
quantitative composition is NOT already proved by the square-system theorem.
Respect that agent's ownership; no competing catalogue was started here.

The unrestricted Polynomial Hirsch goal still requires a polynomial ORIGINAL
ordinary-edge bound for arbitrary carriers. Local recoverability alone does not
bound the total support/image catalogue or establish a short route. Keep the
few-level/aggregate structural assumptions from #277 wherever they are needed.
No fresh authenticated root/leaf mission poll or general diameter claim is made.

Read live STATUS, all five project instructions and current PR heads/comments
before resuming. #210, #270's blocked companion and other owned branches remain
untouched. Root STATUS was not overwritten. Lean4.30.0/Mathlib
c5ea00351c28e24afc9f0f84379aa41082b1188f, protocol0.10.4, workflows, allowlist,
duplicate safeguards and trusted verify/publish credential isolation are unchanged.
