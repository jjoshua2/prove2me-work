# Positive-circuit rank continuation

Base: merged #218 at 89bbe65dd21710c6feb36fe4f0e1e633ab0159fb.
Branch: proof/positive-circuit-rank-cutoff.
Packet: research/publication_packets/positive_circuit_rank.

The previous conversation-only finite-circuit draft is superseded by accepted
#218 and must not be resubmitted. #219 handles the distinct allocation bridge;
its latest inspected gate is 34781016108 at proof SHA
9d3aea2f4120f44a6c43b882d79c9f6f7fcb00c6. No duplicate gate was posted there.
#210 is reserved to the other agent and has not been modified or triggered.
#208's existing pending submission is not duplicated. Existing accepted packets,
Lean/Mathlib pins, Actions workflows, allowlist and secret separation are intact.

The new self-contained 168-line source proves signed restricted-kernel
uniqueness from POSITIVE support minimality, proves the converse, and derives
support cardinality <= dim(range(A))+1 using an explicit injective linear map.
The exact minimality input is supplied by #218's already accepted circuits.
This is the previously open rank cutoff, not a duplicate finite-test theorem.

Source SHA-256: 5bcb41a1327da8909bfff682397382c22be6223a052b6136bfbed47d5e834382.
The statement's type text is copied from theorem solution. There are three
axiom printouts, no admissions, and no custom declarations in the preamble.
These are structural observations, not a Lean or Prove2Me verdict.

Local Lean/Lake lookup found no compiler. Direct toolchain download failed DNS.
No local compilation is claimed. Local reproduction in a configured checkout:

    lake env lean research/publication_packets/positive_circuit_rank/solution.lean

The requested hosted gate is one NEW top-level comment on this new open same-
repository PR, not on #210 or #219:

    /prove2me publish research/publication_packets/positive_circuit_rank

A separate coordination comment on #219 was blocked by the tool and was not
retried or posted through another route. That is not a workflow defect or a
reason to change credentials, security policy or secret separation.

Replace this preparation state with the observed new-PR comment/run/SHA and
actual compiler, axiom and authenticated publication receipts. If the prepared
proof fails Lean, keep the explicit compiler blocker and repair locally before
any further hosted gate; do not make Actions an edit/compile loop.

Remaining mathematical work after verification: formal composition restricting
#218's universal test family to low-cardinality supports; correspondence with
the executable exact nullspace enumerator; support-optimality elimination of
x in the allocation tests; arbitrary residual ordinary-edge routing. No proof
of Polynomial Hirsch or new root dependency is claimed.
