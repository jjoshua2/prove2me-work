# PR #306: alternating-complement 2r+1 exchange routes — ACCEPTED

Read current STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and live PR
heads/comments before taking work. This update supersedes the earlier compiler-
blocked handoff, preserved verbatim as verification/alternating-complement/
first-gate-handoff.md. No accepted or pending packet needs another trigger.

## Actual accepted state

`Hirsch.alternating_complement_exchange_routes` is ACCEPTED; trusted publisher
readback is Proved. Theorem640da3d5-6767-4a08-bdbc-70be357466af,
submission1bc5e00d-3233-4c03-a914-8c8ec6168272.
Frozen proofba1b6db2200e659bfd2970ca635da800a3dd0d51, run35400146836.
Actual new top-level trigger5736776000, resolved acknowledgement5736777333,
authenticated verdict5736803354 were read back. Gate/verify/publish completed
successfully; report-verify skipped. Do not resubmit.

Driver, solution and exact target all compiled with exit0. Five transitive
reports contain only propext, Classical.choice and Quot.sound. The source is
382 lines/16004 bytes, blob36d626c9e9dc495a8866cb4eec6528bcec6b7668,
SHA256f92e3db7370b14aad8c27fe6648891742b4ed47f7c3def06ac9bb232878f472f.
The saved proposal is now the fully verified source, not still an uncompiled
next action. The historical proposal filename is retained for provenance.

First gate35396849974 failed before registration/submission at three diagnostic
roots: Fin successor reduction, reserved internal prefix identifier, no-progress
dsimp. The EXACT saved correction addresses those sites and nothing mathematical.
The entire public statement AND assembly suffix, assumptions, bound and metadata
are unchanged. This was the second compiler gate and first actual platform
submission; exactly one new trigger in this continuation. The earlier failure
is not retroactively a success. No proof edits followed the passing validation.

Read packet accepted-evidence.md, raw publication-receipt.json and packet-audit.json.
All five frozen file hashes and all four original archive hashes match. Raw
compiler logs, audit, manifest and publisher receipt are separate from derived
readbacks. Live Proved is the trusted publisher's authenticated readback, not a
second direct platform poll. No fresh mission-root/leaf status is claimed.
Local Lean was unavailable; the pinned hosted compiler supplies the verification.

## Exact positive route mechanism

Input: two maps h,k:Fin r->Nat, strictly increasing, values below m, with
h_i mod2=(b+i)mod2 for some b<2 and similarly an independent phase for k.
Output: a constructed walk of at most2r+1 nontrivial single-label exchanges.
Every intermediate hole set has cardinality r, stays in range m and has an
explicit legal alternating enumeration. Selected complements have cardinality
m-r and every transition is a nontrivial one-label exchange there too.

Order and parity prove h_i>=b+i. Replace holes from left to right by b+i; each
stage preserves order, bounds and parity. Each endpoint packs in at most r
exchanges. Anchors {0,...,r-1} and {1,...,r} differ in only one boundary label.
Concatenate source packing, the phase crossing, and reverse target packing;
finite induction removes every stationary step. No short schedule is assumed.

r0, r=m, m0 and coincident endpoints are included. Walks may revisit vertices,
lose target labels, or be much longer than shortest paths; none of those
stronger properties is in the accepted statement. No numerical score enters.

## Remaining original-geometry composition

The ORDER-ONLY route is now formally closed. Do not publish another child that
assumes this same short exchange sequence. The next distinct task must bind
actual original moment vertices to these configurations and transfer every step.
For sorted holes h_i<h_j the number of selected labels between them is
h_j-h_i-(j-i); evenness is alternating indexed hole parity. The exact finite
enumeration/cast bridge still needs its own formal assembly.

#302 owns the full numerical/Gale-evenness catalogue equivalence; inspect its
current receipt and respect ownership. #300 owns separated-pair geometric
packing. Accepted #299 supplies complete root reconstruction and #295 supplies
whole original exposed segments for vertices sharing d-1 rows. Neither geometry
nor catalogue admissibility may be inferred merely from the Python checks.

Once those interfaces are actually composed with r=m-d, this construction would
yield a class-specific2(m-d)+1 bound. That is NOT yet a theorem of this packet,
not a new best classical cyclic-polytope result and not unrestricted Polynomial
Hirsch. Arbitrary carriers need additional geometry beyond the alternating-hole
structure. Keep both starting phases/negative-mean cases rather than restricting
the interpretation to positive paired-root vertices.

## Supporting regression, repeated this continuation

The unchanged217-line script tests13724 endpoint pairs/77806 exchanges on66
small models with596 configurations. Independent shortest-path totals are30480.
12593 routes are nonshortest,3651 repeat a vertex and11264 lose an acquired target
row; these adverse results are deliberately preserved.585 rational moment instances
check5011 original rows including221 negative means. Eight selected larger cases
reach m10000 without full graph enumeration.53 saved records/638 edges replay
with construction disabled; six malformed controls fail.

The COMPLETE24690-byte report and536352-byte fixture are byte-identical to the
prior outputs. Source SHA256229922781bbc8e84c91e4ee35fcd71dc2dcea809551bbfa0079f260dbe8bdcb5;
reportfda50f2890b7ca82751505b8f6913d6da34ce30ee2fdec29233f62fa82ac8f64;
fixture933eb66f2f6222f077ba56cdbac6e7a0d5cd93395b57d8bd4fdac8abb548fb3d.
Full raw fixtures and original archives accompany the export and regenerate:

    python3 scripts/test_alternating_complement_routes.py --out /tmp/complement-tests

Python and JSON are not kernel-certified implementations. The accepted theorem
is a separate universal proof. Root STATUS was not overwritten beneath concurrent
work. #304 was already accepted and not submitted again; #300/#302, other owned
branches and reserved #210 remain untouched. Lean4.30.0/Mathlib pin, strict0.10.5
protocol guard, workflows, actor allowlist, duplicate checks and trusted
verify/publish credential separation are unchanged.
