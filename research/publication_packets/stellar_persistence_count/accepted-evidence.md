# ACCEPTED: finite stellar persistence and flag completion count

Hirsch.stellar_persistence_count is ACCEPTED. The trusted publisher's
authenticated readback is Proved. This supersedes the earlier prepared/compile-
only statuses of this packet. Do not resubmit it.

- PR: https://github.com/jjoshua2/prove2me-work/pull/281
- Theorem: 5d525d51-5d42-4dac-a3dd-91ea83902e77
- Submission: 2807f578-7ed5-4be8-aa4a-4bc036ac3101
- Accepted proof SHA: 97d58b7d247c4661e437058e2ca2be34c15e63d5
- Successful run: https://github.com/jjoshua2/prove2me-work/actions/runs/35154778307
- Actual trigger: https://github.com/jjoshua2/prove2me-work/pull/281#issuecomment-5705107861
- Bot verdict: https://github.com/jjoshua2/prove2me-work/pull/281#issuecomment-5705143018
- Verdict timestamp: 2026-09-16T21:56:19Z
- Source SHA256: 2b579f45c887c6ccc44b1caaf2a0686c90c9634fd080cb4010af36da18f83959

## What is formally established

For t actual forward stellar subdivisions on finite supported downward-closed
face families, each at a genuine face of at least two labels and with a fresh
vertex, let A be ANY finite certified initial subfamily of minimal nonfaces.
If all terminal minimal nonfaces have size two, the theorem proves

    |A| + t <= choose(|V(0)| + t, 2).

The actual stellar membership rule is in the public statement. Persistence,
injectivity and cardinality growth are derived, not assumed. The proof gives
canonical minimal descendants, proves they are distinct, derives the additional
born nonface at each step, constructs the tracked finite family by induction,
and counts it inside the terminal two-element subsets. Completeness of A is
not required. Empty A and t=0 are included.

This is the finite combinatorial core of #267's written obstruction. It DOES
NOT make the cyclic-polytope exponential construction, its geometric realization,
original-edge transport, or the Polynomial Hirsch conjecture formally proved.
Those interfaces remain separate. Inverse moves and arbitrary non-stellar
subdivisions are not part of the statement. No new universal diameter bound
or historical-priority claim is made.

## Actual compilation and submission history

The initial295-line candidate reached Lean in run35154274683 and failed on
one redundant successor rewrite at line255. Its substantive persistence/birth/
step-growth helpers compiled, but the final sequence theorem did not. Publication
was skipped; that run created no theorem registration or submission.

The correction deleted ONLY Nat.succ_eq_add_one from the rewrite list because
the target already had i+1. No type, hypothesis, public statement, problem.json
or explanation changed. The corrected295-line source compiled successfully:
driver, solution and statement all exited0. All five audited declarations
use only propext, Classical.choice and Quot.sound. The corrected proof's first
actual platform submission was accepted. It is not claimed that the first
compiler attempt passed unchanged.

The user-requested NEW top-level PR comments actually launched both gates;
there was no workflow_dispatch, new workflow, token, permission or pin change.
The original local runtime has no Lean compiler: the Lean evidence is the
pinned GitHub job. The actual Prove2Me acceptance is distinct from that job.

## Preserved independent artifact checks

Verified artifact10470098719 archive SHA256:
71e0569fdb94d0f174e1bc5c37be5dc24902042e406272a9892891367629d4af.
Publication artifact10470583174 archive SHA256:
14b979e88ed7a331804c79fa295b9bcd172730969654dfd3b412379baa8cc6e8.
Both original archives were downloaded and independently hashed. All five
frozen source/driver/statement/metadata hashes were recomputed. The frozen
solution, problem and explanation match the corrected local packet byte-for-
byte. Raw packet audit, verified manifest, driver log and publication receipt
are committed unchanged. The two resolved request archives preserve the initial
and corrected proof SHAs; both archive digests were also checked.

publication-receipt.json is the exact aggregate receipt from the publisher.
The original publication ZIP contains only that receipt and the generated
comment, not individual raw platform API responses. The derived readback JSON
is explicitly labeled. Proved is the trusted publisher's authenticated readback,
not an additional direct platform query by this chat. No missing API response
is invented. Post-verification commits add only evidence and do not change the
accepted proof bytes.

The independent finite-semantic/signature suite passes and repeats byte-for-byte
in a clean directory:114 complexes,515 actual subdivisions (77 larger than
edges),1204 old descendants,80 four-step incomplete-subfamily chains,320 chain
steps and61 flag terminal cases. These Python checks support the interpretation
but are not the Lean proof or a formally verified Python implementation.

## Next interface

The finite counting core is now an accepted reusable result, not an uncompiled
research target. Reuse this exact statement and receipt instead of publishing
another copy. A future fully formal obstruction needs the separate geometric
family supplying a large finite A and its asymptotics. A conjecture solution
still needs an original-edge upper bound; this theorem constrains one full-
refinement strategy rather than producing such a bound. Other agents' pending
proofs and research branches were not modified or retriggered.
