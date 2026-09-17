# ACCEPTED: ordered moment minimal nonfaces

Public theorem: `Hirsch.moment_curve_ordered_minimal_nonfaces`.
Theorem ID: `07cdedd0-db22-48e8-897e-d9d3ab04bcf1`.
Submission ID: `83b6f1bb-cd20-431f-92ff-6f1eb201a917`.
Trusted publisher verdict: ACCEPTED; authenticated readback: Proved.
Proof head: `56f1b0b4e83300b55a055a798a7f0be1d0f47400`.
Run: `35176922050`; PR #288.
Publication trigger: issue comment `5707849370`.
Verdict: issue comment `5707873841`, `2026-09-17T03:09:39Z`
(September 16 at 23:09:39 America/New_York).

The original 606-line proof passed its FIRST pinned compiler/axiom gate and
FIRST platform submission unchanged. Driver, solution and statement exited 0.
All five transitive proof reports list only propext, Classical.choice and
Quot.sound. Harmless deprecated-tactic and unused-tactic warnings in reused
accepted proof bodies remain in the raw driver log; they were not suppressed
or edited away. The target statement has its expected placeholder; the actual
solution imports no target and contains no admission.

## Exact theorem and what is newly derived

For an injective real parameter map a on m original labels, choose any embedded
chain b of 2k+3 labels whose PARAMETER values strictly increase. Let N be the
k+1 labels at its odd zero-based positions. In the original dimension-2k
mean-centered moment inequalities, the theorem establishes:

- |N|=k+1;
- no feasible point makes every N row tight;
- every proper T subset N has a feasible point whose exact tight-row set is T.

The original mean is over ALL m labels, not just the selected chain. No
barycentric sign, affine dependence, rank, support witness, incompatibility or
minimality certificate is a premise. k=0 and empty proper subsets are included.
The term original-row family is literal: this packet alone does not formalize
that every presentation in every boundary case has a polytope facet interpretation.

The new proof splits the barycentric denominator into the positive lower
factors and the negative upper factors. There are 2k+2-i upper factors, so the
weight is negative exactly when the selected rank i is odd. The accepted
nonzero slack-polynomial argument then supplies a strictly slack odd row at
every feasible point. Injectivity gives the exact odd-set size. Every proper
subset has size at most k, so the accepted small-face theorem constructs its
exact witness. This combines incompatibility and proper-subset feasibility
into genuine inclusion-minimal incompatibility for the selected set.

Both accepted namespace bodies were reused BYTE-FOR-BYTE, excluding only their
old root solution/print suffixes:
#285 blob3506c3b28278e52412e7867b08f81c096b836334, and
#286 blob6050e16e234b64011ea8bb8b643cc9461c327ce3.
They are actual proved code, not newly assumed helper statements. Their old
public targets were NOT registered or submitted again. #285's still-owned
integration and every other agent's branch are untouched by this packet.

## Actual publication and raw evidence

Exactly ONE NEW top-level comment was posted on the open same-repository PR:

    /prove2me publish research/publication_packets/moment_ordered_minimal_nonfaces

The bot resolved the exact head above. No dispatch, workflow, permission, token,
compiler pin or trusted-main secret split was changed. Local Lean/Lake was
unavailable; formal verification is the pinned hosted run, not the rational
regression re-labeled as compilation.

The original request, verified packet and publication ZIPs were downloaded.
Their independently recomputed SHA256 digests are:

    request: 00a4a7919cced4782cfd1a1e6a5ac826650a2fb11ac43d0b63c63a3c44addc3e
    verified: f6f5a8f7828942b6c8abd7a0937820b2f842f8f9c0228344bcfc9374933658e8
    publication: b921728da6b88f282d9bbf41be2691ff10466e809e47ea5fa16d44c40a3b1d26

All FIVE frozen source/driver/statement/metadata hashes were independently
checked against the verified manifest. Solution, problem and explanation match
the prepared packet bytes exactly. Source SHA256:
`0cb180af7915af3e9da23aee512e4f5930b389a876b4bb6e014c3e69ea467ae6`.
The raw audit, full driver log, verified manifest and aggregate publication
receipt are preserved unchanged beside this note. Artifact readback is an
explicitly labeled local record, not an invented direct platform response.
The publication ZIP contains an aggregate receipt and generated comment, not
individual raw API-response objects. Proved is the trusted publisher's
authenticated observation; the chat made no separate fresh platform query.
Post-verification additions do not modify any of the four submitted files.

## Reproduction and tests

    python3 scripts/test_ordered_moment_packet.py

The independent rational test covers120 arbitrary nonuniform/scrambled-label
cases,840 sign checks,720 moment equations,1368 proper-subset witnesses,
17256 original inequalities,14520 strict rows and360 feasible-point tests.
Three larger samples in dimensions16/32/64 check each immediate proper subset
plus the empty set, not the entire exponential catalogue. A separate exhaustive
small integer-family application checks76 minimal sets and1992 proper-face
witnesses. Eighteen stored consumers pass with witness production disabled;
nine malformed assumptions/certificates are rejected.

A fresh directory containing only the standalone test and the source/metadata
inputs reproduces both the full report and the557163-byte fixture byte-for-byte.
Exact replay hashes are in research/ORDERED_MOMENT_PACKET_REPLAY.json. This is
supporting software evidence; Python and its JSON parser are not Lean-verified.
The full original artifact archives and detailed fixtures are in the conversation
bundle. Repository tests regenerate the fixture without any earlier bundle.

## Remaining interface

This closes the ordered-sign and per-chain minimality bridge left after #285
and #286. It does NOT yet formally select separators for EVERY (k+1)-subset
of odd integer labels, count the complete family by a binomial coefficient,
assemble that family with accepted #281, or prove the full geometric realization
and exponential asymptotics. Those are distinct remaining formal interfaces.
The current universal-in-k ordered-chain theorem is not finite-sample inference.

Neither this incompatibility result nor #267's refinement-size obstruction is
an original-edge upper bound or a solution of Polynomial Hirsch. A conjecture
solution still needs a uniform polynomial route construction or another valid
upper-bound argument. Reuse this accepted target rather than resubmitting it.
The older source-manifest PREPARED status is historical and superseded here.
