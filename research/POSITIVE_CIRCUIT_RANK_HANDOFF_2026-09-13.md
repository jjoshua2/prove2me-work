# Positive-circuit rank handoff: ACCEPTED and live Proved

## Accepted theorem

PR #222 proves the rank cutoff left separate by accepted #218/#219.

- Theorem: `Hirsch.positive_circuit_signed_kernel_and_rank`
- Theorem ID: `864c87b2-cf47-469a-884a-4a6352e0ab23`
- Submission ID: `f60b3d5d-7617-4b01-a11d-121b24d9ff42`
- Final audited proof head: `c3eff585fd047892f28a5287752ab015767ab29b`
- Final Actions run: `34783103887`
- Authenticated status: `ACCEPTED`; live theorem readback: `Proved`
- Packet: `research/publication_packets/positive_circuit_rank/`

The theorem says that for a real linear map `A`, a nonzero nonnegative null
vector has support minimal among all nonzero nonnegative null vectors iff every
SIGNED null vector supported there is a scalar multiple of it. It then proves

    |support(x)| <= finrank(range A) + 1.

The proof uses an explicit minimum-ratio subtraction and an injection into
`range(A) × R`. No full-rank, generator-independence, boundedness, simplicity,
Farkas, feasibility, or diameter premise is added.

## Verification and publication receipts

The first hosted attempt exposed one elaboration-only gap in the zero-coordinate
branch of the extension map. Commit `29fed598b7e8d0b2e99d5f5bd6c2ddb4edf780c1`
changed only that proof branch by deriving `x i = 0` from `¬ x i ≠ 0`; theorem
statement and packet metadata stayed unchanged.

The corrected packet compiled in run `34782262056`, but the old trusted
publisher discarded its problem-registration `job_id` after a 180-second poll
timeout. PR #223 fixed that infrastructure without changing the actor allowlist,
secret separation, workflow permissions, or Lean pin. The safe-resume run
`34783103887` recompiled the exact packet and the publisher reported
`registration: REUSED`, so it found the theorem created by the earlier
registration rather than submitting a duplicate problem.

Final frozen evidence:

- driver / solution / statement exit codes: all `0`
- axioms: only `Classical.choice`, `Quot.sound`, `propext`
- solution SHA-256: `5360f2a04a68b580552470ba42d1fa011eec5a73275c1c9b7766475fea028ddc`
- statement SHA-256: `344e4bbd9fdbc436aa75fa8bd6c65bd4634a1d42e3abc13d89584282e430483b`
- verified artifact `10325579396`, digest
  `sha256:485c3b4c47c4a1121bbe7eba88062630c7c9c743f5a877c0da7a8fa9ff494809`
- publication artifact `10325721762`, digest
  `sha256:29acb077f7bb6bf94152b7bd6f0f37c1a1a47934ae42c29f10ce0c7f6bf39d78`

`packet-audit.json`, `manifest.json`, `publication-receipt.json`, and
`accepted-evidence.md` are preserved beside the packet. The trusted publisher
also requires byte-for-byte accepted-source readback before returning ACCEPTED.

## Remaining exact frontier

Do not resubmit this packet, accepted #216, #218, or #219.

The rank cutoff now justifies restricting a true positive-circuit search to
small supports. The remaining enumerator bridge is to connect exact rational
restricted-nullspace computation and normalized positive-ray output to the
actual support-minimal Circuit predicate. Another agent announced work on the
distinct constructive decomposition of arbitrary nonnegative null vectors; do
not duplicate that line.

The original-point optimization bridge is handled separately by PR #221. Once
that theorem is accepted, compose it with #219: for each allocation multiplier
`(lambda,mu,nu)`, set `K = sum lambda_i*h_i - nu*t`; an original-H primal/dual
support certificate collapses #219's universal `x` test to the scalar budget
`K <= lambda·b - alpha·b`. That is the next clean extraction composition.

#210 remains reserved to its other agent and was not modified or triggered.
Arbitrary residual ordinary-edge routing and Polynomial Hirsch remain open.
