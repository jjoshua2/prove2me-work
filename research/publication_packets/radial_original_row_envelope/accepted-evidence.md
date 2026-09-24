# Accepted: original-row radial envelope in arbitrary dimension

Theorem: `Hirsch.original_row_radial_max_envelope`.
Theorem ID: `b14806b3-8f55-41f5-a98a-8e668394a960`.
Submission ID: `ccc4850c-ffa8-4e0a-8cec-dd856d7c530c`.
Frozen proof: `3a8ac361ca2a02f9e3c51205daec5f34446a0dca`.
Run: `35952167164`; request `5807080689`; acknowledgement `5807083009`;
accepted bot verdict `5807134838` at 2026-09-24T03:41:20Z.

The downloaded, unmodified publisher receipt records PUBLISHED / ACCEPTED /
Proved. Proved is the trusted publisher's authenticated readback, not a new
independent platform or mission-root poll. No further submission is needed.

## Complete proof and verification

The 561-line, 24594-byte source has Git blob
`5aa85241c966d6a2ebfc355f0f911f1a66754e22` and SHA256
`2cc1309ad076230fb3af3dada0d4059764c41dbf909e856be17b7dfeec863c5f`.
The saved repair adds exactly one beta-reduction line in scaled_tight. The
public type, all other proof text, accepted helpers, problem.json and
explanation.md are unchanged. No post-acceptance proof edits were made.

Driver, standalone solution and exact statement compile with exit 0. All eight
reports in each complete proof log contain only propext, Classical.choice and
Quot.sound, including solution. No sorryAx remains in the proof. The separate
statement-only placeholder is not proof evidence. Gate107482820962,
verify107482857301 and publish107483154060 succeeded; report-verify107483154849
was skipped. Mathlib remains c5ea00351c28e24afc9f0f84379aa41082b1188f.

Keep the three stages of history distinct:
1. Run35945514083 failed compilation of the original source.
2. Run35950971172 compiled the repaired source but publication stopped at the
   exact protocol guard before registration or proof submission.
3. After separately reviewed maintenance #342 merged as
   c1697e8daed6aac8616cdc9ff22bfef39ad43ad1, run35952167164 compiled the SAME proof
   and its first actual platform proof submission was accepted.

The accepted publication was already complete when this integration continuation
read it. This continuation downloaded and independently checked the artifacts;
it did not create the compatibility change or the publication resume request.
No redundant registration, proof submission or compiler run was triggered.

## Exact mathematical scope

For arbitrary d, finite real C, exact conv(C)={x : all m original inequalities
hold}, and an actual target vertex v, derive a linear h strictly positive on
P without v. For positive a the rows transform exactly into

    A_i(v+y/a)<=b_i  iff  A_i(y)<=a*(b_i-A_i(v)).

Target-tight rows remain directional constraints; their zero slacks are never
divided out. On normalized target-cone directions, the positive-slack original
rows give a positive attained maximum and exact radial feasibility threshold.
Every non-target actual original vertex attains the envelope, retains ALL
original tight-row labels and has a distinct normalized vector. Every genuine
original exposed edge between non-target vertices has an original row tight at
both endpoints and slack at v. These are conclusions, not supplied oracles.

Exact finite-hull/H equality and actual target extremality remain assumptions.
There is no dimension-two restriction. This is an original-row geometric
interface and an edge-charge witness, NOT a polynomial route construction or a
bound on repeated charges. It does not assert a face-lattice/graph isomorphism,
an efficient H-to-V algorithm or a solution of the Polynomial Hirsch mission.
The next conjecture-facing gap is to control repeated original-row charges along
an actually constructed ordinary-edge route without using an expanded vertex
inventory as the complexity parameter.

## Raw artifacts and independent preservation

The complete successful artifacts are under
`research/verification/radial-original-row-envelope/accepted-run/raw/`:
12 verified files, two publisher files and the exact resolved request.
All 15 files match the downloaded originals. Their combined Git tree is
`b0bed6fb7d7d39f5023dcdfdcd8fd4d9243a2352`, checked independently from local bytes.
The raw receipt is also copied to this packet as publication-receipt.json.
All five frozen input hashes, all 16 printed axiom reports and the exact public
type were checked. Those five input files also match the earlier passing,
protocol-blocked artifact byte-for-byte. These are offline integrity checks,
not another Lean run or authentication of arbitrary receipt data.

Original successful ZIP identities:
- request10788373865: 314 bytes; SHA256
  a691969804b339d1d446ac0f0bc59dac5b52557effe383a2880330397873d5cc;
- verified10788688281: 23185 bytes; SHA256
  498fe37baeea2cc885aaac1d81d0af1cde7e241d4f09f077c61cbfb921444aea;
- receipts10789176776: 906 bytes; SHA256
  9c5205b19e8b7aa7fa3a1b8342dba3ce5b9ea4607e0967355893d2d605269804.

Complete compiler logs are preserved; full runner archives and individual
platform API bodies are not claimed to have been copied. Existing first-attempt
files remain unchanged. The previous handoff is preserved beside this readback.

The earlier recorded rational checks remain supporting evidence: 13 complete
small catalogues with 181 vertex observations, 1946 tight-row identities,
281 edge/target witnesses and 12 rejected controls; selected 8/16/32/64D cases
are not complete catalogues or global-rank checks. This integration did not
rerun those geometric tests. Python/JSON are not kernel-verified. The earlier
supporting-script upload block remains respected: no script upload, retry,
renaming or alternate route was attempted.
