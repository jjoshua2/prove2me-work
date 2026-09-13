# Finite positive-circuit continuation

Base main: a7db9296e6645e92048f37089f0645f8a292f27c. Read together with STATUS.md and CONTINUE_HIRSCH.md; their older frontier descriptions do not replace live PR inspection.

## Ownership and existing receipts

Only #208 and #210 were open at selection. #210 is assigned by the user to another agent and was read only, never changed or triggered. Its observed head was 9b077abd1c537a7388acbaefd0f771ad63261b5c. #208 head was 6446efee979b57d07b46215ec3f64efa1332329f; its existing submission 2a2dd9bd-9ee5-43fa-bc04-def26a5a2a98 is pending in that handoff, not freshly polled here. Do not resubmit it.

#216 is merged. Accepted theorem a6e2a38d-00e3-46d6-b232-7cddee5e30e1, submission 2976ce68-c33c-4cab-b48e-8a7f46be211a, run 34776731744, and original source 115b3ede788bca52bcac568d1aa05e62a0d92559 are preserved unchanged. Its accepted-evidence.md records authenticated Proved readback. This continuation neither republishes nor reproves that compact-convex theorem.

## Concrete new packet

research/publication_packets/finite_positive_circuit_tests/ contains solution.lean, problem.json, explanation.md and a clearly labeled preparation record. The theorem is Hirsch.finite_positive_circuit_dual_tests.

For any real linear map A:R^n->R^k, choose one nonzero nonnegative null vector per minimal support and zero on unused support slots. This ONE finite family detects nonnegativity of EVERY subsequent linear functional on the entire nonnegative kernel. The direct proof reduces any negative certificate to a negative positive circuit and proves positive-ray uniqueness on a circuit support. Circuit completeness is proved, not an input. No new feasibility, Farkas or diameter axiom occurs.

The 242-line standalone candidate imports Mathlib only. Its published type uses Mathlib symbols only; helper definitions are not in the problem preamble. The committed Lean 4.30.0 / Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f pin is unchanged. No workflows or security configuration are changed.

## Verification state at preparation

Local lean/lake are absent and container DNS cannot resolve github.com. No local Lean compilation or axiom audit is claimed. Packet/text checks do not establish either. A single prepared comment-triggered hosted publication gate is appropriate; ordinary Lean errors must then be repaired locally, not by speculative repeated Actions runs. Append the actual comment, resolved proof SHA, run/jobs/artifacts and authenticated verdict once observed. No Prove2Me submission exists for this packet at this preparation commit.

Exact local command in an environment with the committed toolchain:

    lake env lean research/publication_packets/finite_positive_circuit_tests/solution.lean

## Precise remaining bridge

This closes the proposed algebraic finite-linear-test ingredient only if its direct Lean candidate passes verification. It does not yet formalize the sharper rank(A)+1 support bound, algorithmic circuit enumeration, or the explicit allocation/alternative adapter taking #216's compact-convex support tests to this nonnegative-kernel criterion. That adapter, preserving all whole-set and support assumptions, is the concrete next geometric obligation. Arbitrary residual routing and the uniform ordinary-edge Polynomial Hirsch bound remain unresolved. No root dependency edge is asserted from merely mentioning either theorem.
