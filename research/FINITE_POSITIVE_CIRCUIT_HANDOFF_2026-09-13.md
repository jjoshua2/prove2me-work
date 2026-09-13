# Finite positive-circuit continuation: ACCEPTED

Read together with STATUS.md and CONTINUE_HIRSCH.md, then inspect live PRs.
PR #218 has completed the algebraic finite-dual-test obligation. The unchanged
242-line proof compiled and passed axiom auditing on its first prepared hosted
gate, then Prove2Me returned ACCEPTED with authenticated live status Proved.

Theorem: Hirsch.finite_positive_circuit_dual_tests
Theorem ID: 8f3c4cc7-be73-4ecf-9e17-816c710e20d7
Submission ID: 3fd7936c-8271-4a24-b342-d60bfd29529f
Proof SHA: ad4345bb17066c91b13d09ab0c8e757cbc5b65c9
Run: https://github.com/jjoshua2/prove2me-work/actions/runs/34778403314
Verdict: https://github.com/jjoshua2/prove2me-work/pull/218#issuecomment-5655650520
Packet and exact receipts: research/publication_packets/finite_positive_circuit_tests/
Do not resubmit or unnecessarily rerun the unchanged accepted source.

## What was actually proved

For any real linear map A:R^n->R^k, choose one nonzero nonnegative null vector per
minimal support and zero on unused support slots. This ONE finite family is
chosen before the objective and detects nonnegativity of EVERY subsequent
linear functional on the entire nonnegative kernel. The direct proof reduces
any negative certificate to a negative positive circuit and proves positive-ray
uniqueness on a circuit support. Minimality is against ALL nonnegative null
vectors, not only the negative certificates. No Farkas, circuit-generation or
feasibility premise is smuggled into the result.

All three compiler exit codes are 0; the four printed declarations use only
Classical.choice, Quot.sound and propext. Source SHA-256:
7b64b82bf4cec0fa348bed86676911eeec2725fccdcf75018e03ac1a418f7520.
Local lean/lake were absent; this was real hosted pinned compilation, not a
claim based on source checks. One NEW top-level PR publication comment was
posted and read back, its resolved request and three artifacts downloaded,
all archive and frozen source hashes checked, and jobs/logs/verdict inspected.
The pre-gate preparation.json is historical; accepted-evidence.md is current.

## Precise next obligation

research/FINITE_CIRCUIT_ALLOCATION_NEXT.md gives the exact fixed matrix
C theta=(-a(G theta),-theta,sum theta), right side d(x,t), and the sufficient
alternative needed to obtain whole-set finite Minkowski tests. The missing
sufficiency must be proved, not assumed. Reuse this accepted algebraic result
and accepted compact-dual theorem #216; do not create another decomposition
claiming that mentioning them proves the root.

The sharper rank(C)+1 support bound, executable circuit-enumerator correctness,
and the whole allocation-to-Minkowski composition are NOT formalized by #218.
The new finite family has at most 2^n support slots, not a polynomial count.
Arbitrary residual routing and the uniform ordinary-edge Hirsch bound remain
unresolved. No full-rank, strict-feasibility, boundedness, simplicity, or new
diameter assumption was added to the accepted algebraic theorem.

## Ownership and preserved prior work

Selection base main was a7db9296e6645e92048f37089f0645f8a292f27c. Only #208 and
#210 were open at selection. #210 remains another agent's work: do not edit or
trigger it without reassignment. Its head then was
9b077abd1c537a7388acbaefd0f771ad63261b5c; it was read only.
#208 head was 6446efee979b57d07b46215ec3f64efa1332329f. Its existing submission
2a2dd9bd-9ee5-43fa-bc04-def26a5a2a98 was pending in its handoff; no fresh
poll/submission was performed here. Do not duplicate it.

#216 is merged and accepted: theorem a6e2a38d-00e3-46d6-b232-7cddee5e30e1,
submission 2976ce68-c33c-4cab-b48e-8a7f46be211a, run 34776731744, original
proof 115b3ede788bca52bcac568d1aa05e62a0d92559. It was not resubmitted.
Lean 4.30.0 / Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f, workflows,
permissions and secret separation remain unchanged. The receipt/handoff
follow-up edits no proof source and needs no new theorem publication.
