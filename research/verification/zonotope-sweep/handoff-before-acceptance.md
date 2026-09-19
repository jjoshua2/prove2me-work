# PR #313: regular zonotope sweep — Lean verified, publication blocked

Read current STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and live exact
heads/comments before resuming. Starting main6b0ed8524c0b16b3e4acbc1f5c73708e2d221082
already contained accepted #310/#311/#312. In particular the old #310 local
repair was superseded and was NOT submitted again. Coordination on #312 is
comment5744118142, posted and read back. Other owned work and reserved #210
remain untouched.

## Authoritative status

Target Hirsch.zonotope_regular_sweep_original_edges.
Packet research/publication_packets/zonotope_regular_sweep.
PR #313 is OPEN/DRAFT. The full proof has PASSED pinned compilation and the
standard-axiom audit; platform publication has NOT succeeded. No theorem ID,
submission ID, ACCEPTED status or live Proved receipt exists from this attempt.

Actual NEW top-level command5744212067 resolved in acknowledgement5744213464 to
proofcaf342b4679820b8e8b12633493884938536135d, run35460242988. Both were read back.
Gate105942681452 and verify105942709293 succeeded; publish105942959283 failed at
version compatibility, report-verify105942959981 skipped. All jobs completed.
Bot5744227133 was read back and reports no publication receipt.

All three driver/solution/target compilations exit0. All five transitive reports
(regularize_on, tied_collinear, mem_crossingSet, regular_sweep, solution) contain
only propext, Classical.choice and Quot.sound. This was the FIRST compiler gate,
with exactly ONE trigger. No compiler failure, proof repair, weakened assumption,
post-gate proof/metadata edit or further trigger. The726-line/30146-byte source
is unchanged, blob097c1df64a2eea944613a4a62eb63edbe9d5ccea,
SHA2563d233db7a1ce78a9376a758af92ce71634f9a0a45887d48384b99dfbc30153f4.

## Publication prerequisite, not a mathematical repair

The trusted client in scripts/publish_projective_small_blocks.py still checks
version==0.10.5. The actual publisher refresh raised the mismatch error BEFORE
registration/submission. Its response version was not logged and is not invented.
Official upstream commit32b755663224d6c3f572406e893e9b10ca652202 is a version-only
0.10.6 release: its complete diff changes one SKILL.md metadata line. See
verification/zonotope-sweep/PROTOCOL_REFRESH_REQUIRED.md for immutable identities.

A separate reviewed trusted-main refresh should retain exact mismatch rejection,
all duplicate guards, API-host restrictions and verify/publish secret separation.
Then check live comments/receipts again before resuming THIS SAME already compiled
packet. Do not change its theorem name or resubmit any newer pending/accepted job.
No publisher, workflow, version guard, skill, allowlist or credentials were changed
in this continuation. Local Lean/Lake was unavailable; the hosted compiler is the
actual formal evidence, separate from all rational/source checks.

## What has now been proved in Lean

Let Z=sum_i[0,w_i] and let f,g be regular on every nonzero generator. Construct k
with the same generator signs and whole target maximizing face as g. For the
straight segment h_t=(1-t)f+t*k, construct the exact finite exceptional set T of
interior nonzero-generator ties, with |T|<=m. At each t in T the ENTIRE maximizing
face is a nondegenerate original exposed/extreme segment with actual extreme
endpoints. At every other t in[0,1], the whole face is a singleton actual vertex.

Include all w_i and contrasts f(w_i)w_j-f(w_j)w_i in a finite test set. Pinned
Mathlib supplies a functional nonzero on every nonzero test vector; finite margins
make k=g+e*h preserve all already nonzero signs. At simultaneous ties, affine
scalar equations force k(contrast)=0, so contrast=0. Regular f then gives exact
collinearity. Parallel/opposite ties remain valid; independent ties are excluded.
Each nonzero generator has at most one candidate root f(w_i)/(f(w_i)-k(w_i));
image/filter reasoning proves both directions of the exceptional-set identity.
The accepted #312 whole-face theorem supplies original edges at every event.
Coefficient saturation proves singleton faces elsewhere and target-face equality.

No generic perturbation, crossing list, collinearity or edge oracle is supplied.
Zero/repeated/opposite/parallel generators, lower rank, d0 and m0 are included.
The complete425-line #312 namespace prefix is byte-identical; its old public
root/prints are omitted and its accepted target is not resubmitted. All five
old manifest hashes and the original verified archive were checked.

## Remaining route and general-conjecture obligations

The controlled-sweep/exceptional-face obligation is closed at the Lean level,
not yet platform publication. Next formal work must order T, identify the
constant chamber vertices on adjacent intervals with the two endpoints of each
edge, and construct a bounded walk. It must also produce regular exposing
objectives for arbitrary requested actual vertices before claiming all-pairs.
Those statements are not part of this packet and not inferred from Python paths.

The count m is segment generators, not original H facets. A polynomial generator
budget for a completion of arbitrary input polytopes remains separate. No
unrestricted Polynomial Hirsch, shortestness, new optimal classical bound or
historical first is asserted. Do not replace the missing original-input budget
by the size of an exponentially expanded auxiliary generator list.

## Reproducibility and preserved raw evidence

The downloaded request10589109280 and verified archive10588748677 have recomputed
hashes04167d0132ac338487330476dfd641b1bb60afd6121463944884bf4bd594be2b and
4708118df35e50cb1b0bfa4c99d269da218866cf3fe9207f232a0e713414d7ba.
All five frozen packet hashes match. Raw audit, manifest, all compiler logs,
request and verified aggregate are separate from derived readbacks. The full
publisher log was read; only an explicitly scoped error excerpt is committed.
No absent API bodies, acceptance receipt or fresh root/leaf poll is fabricated.

The standard-library Fraction regression checks165 sweeps:125 crossings,
46 parallel-tie events,39 zero generators,9462 Boolean representations,
369 whole-face and19832 singleton-support checks. Four selected d8/16/32/64
systems avoid full enumeration. Thirty-four saved records audit with perturbation
construction disabled; four forged records fail. The naive unperturbed square
sweep's independent simultaneous tie is retained. The test constructs sample
walks, but these are not a completed Lean route theorem or verified JSON parser.

Clean script-only replay matches the1791-byte report and38439-byte fixture:
390664da822e557169ffa0de181b509962c55114a757112da5e7ea79949fe670 and
fef9b004e1b0593b968311f9732e5d607f97a98c0e2000dab99567b62b72e4eb.
Script SHA256f5a8544e29d67f1f4da76c57d4ba528773d27a8daca5e03386ac1e9447996469.
Full original ZIPs and fixture accompany the bundle and regenerate with:

    python3 scripts/test_zonotope_sweep.py --out /tmp/zonotope-sweep

Existing main files, root STATUS, other owned branches, #210, Lean4.30.0/Mathlib
c5ea00351c28e24afc9f0f84379aa41082b1188f and all trusted controls remain unchanged.
Consult live PR metadata for the evidence head, distinct from the frozen proof.
