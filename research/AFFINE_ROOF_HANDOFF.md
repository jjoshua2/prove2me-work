# PR #326: independent affine-roof routes — first full gate failed

## Current state and exact identity

Keep OPEN/DRAFT. No new theorem has been registered or submitted from this run.
Repository: jjoshua2/prove2me-work.
Branch: proof/independent-affine-roof-routes.
Target: Hirsch.independent_affine_roof_original_routes.
Packet: research/publication_packets/affine_roof_routes.
Tested proof: 3fedb7d9ddd9c40235e304ab71db126f52016d9d.
Base / trusted main: 34696607bb8f6298bb400d9ce9a0903dc078c157.
Later evidence-only heads do not replace the tested proof identity.

Actual NEW top-level publication comment 5769724425 was posted and read back.
Bot acknowledgement 5769725445 resolved that proof to Actions run 35673924236.
Gate 106576289323 succeeded. Verify 106576318567 failed driver compilation,
exit 1. Report-verify 106576548751 and publish 106576548916 were skipped.
Separate solution and statement compilation were not reached. No complete audit,
verified packet archive, theorem/submission ID, receipt, ACCEPTED or Proved result
was produced. There was no independent platform/root poll or second trigger.

## Mathematical result intended by the complete candidate

The base P is BOTH conv(C), for finite 0/1 C in ambient R^n, and the original m
halfspaces D_i x<=b_i. Add k INDEPENDENT coordinates with original bounds
0<=y_j<=c_j+A_j x, where every affine height is strictly positive throughout P.
For any two ACTUAL extreme points of this ORIGINAL Q, the written argument and
complete candidate construct a route through actual Q vertices, with distinct
successive endpoints and whole IsExtreme segments, satisfying L<=n+k and L<=m+k.
Q has m+2k displayed original inequalities. k is unrestricted and may grow.

Fixed normalized fiber coordinates define affine base sections, deriving that
an actual Q vertex projects to an actual base vertex. A strict vertical convex
combination rules out intermediate roof values. Thus the Boolean boundary
choices are derived, not assumed. Fixed Boolean sections lift entire extreme
base sets and their full edges. The fiber over a base vertex is extreme; whole
positive-box coordinate edges transfer to original Q. Hamming induction costs
at most k fiber edges; the accepted #322 0/1-base theorem supplies at most n
base edges, lifted along target boundary choices. A separate midpoint/kernel
argument derives n<=m from the original base rows and an actual base vertex.

No graph, labels, vertex catalogue, active basis, rank, base walk or cheap
residual phase is supplied. Nonsimple/lower-dimensional bases, redundant base
inequalities, zero base/fiber dimensions and equal endpoints remain included.
The exact H/hull equality, 0/1 base, independent intervals and strict positivity
are structural premises, not proved for arbitrary carriers. No full graph
isomorphism, shortestness, all-facet nonrevisiting or polynomial-time H-to-V
claim is included. This is NOT unrestricted Polynomial Hirsch. The unchanged
packet explanation gives the full argument and classical attribution.

## Exact failed source and reported issues

Tested source: 1601 lines / 71596 bytes; blob
d87643fecff675dbd12694473f5ba39bcaa7a86b; SHA256
0b5b6c0ba031d3418a3c25d6a49e8f943bb6a4d9c3519c7aa76dfbbc888d3ef2.
All three remote packet blobs match the prepared bytes. Accepted #322's first
973 lines / 41934 bytes are byte-identical; its old public root/final prints are
omitted, not resubmitted. All five dependency manifest digests pass.

The compiler reported syntax errors at lines 1051, 1510 (two), 1529 and 1569;
Prod.ext rfl inference failures at 1069, 1142 and 1179; and Fin value goals at
1473/1474. Unknown zero_of_positive_mix at 1157/1161 is downstream of its syntax
error. At the final prints original_row_count and solution are undeclared.

All five inherited finite-proof reports are standard-only. The five emitted new
reports (extreme_classification, lift_extreme, vertical_edge, fiber_route and
roof_routes) contain sorryAx from failed elaboration. Neither the new chain nor
the public root is verified. No admission was written in the candidate source.
The scoped transcript retains every error header and printed axiom report, with
selected goal excerpts; timestamps and long contexts are omitted. The complete
decoded verifier log was read through cleanup, but this is NOT a raw log archive.

## Separate UNAPPLIED and UNCOMPILED repair proposal

research/verification/affine-roof-routes/proposed-local-repair.patch changes:
- comparison whitespace to avoid unintended adjacent notation parsing;
- three product equalities to apply Prod.ext before solving the first component;
- the two finite-index value equalities to use complete simplification;
- reserved local identifier prefix to firstLeg, with secondLeg for the suffix.

The proposal also applies the same comparison whitespace to problem.json's
formal_statement so its text remains matched to the proposed public type. No
intended binder, mathematical hypothesis or conclusion is changed. Public type
and root-proof text match the originals after removing whitespace; they are not
byte-identical and parser/type correctness still requires Lean. The accepted
973-line dependency prefix and explanation are unchanged.

Proposed source: 1608 lines / 71702 bytes; blob
4ecc055d476fa69133903c8eeef8347f04c5e1ca; SHA256
a8bf4aa83140f687318dc3cc6f33a57752c4e612d791a9d480f7b1529b0aae75.
The complete two-file patch applies and reverses exactly. It is NOT applied to
the publication inputs and NOT compiled. Further errors may appear. Do not call
this a passing repair or start a speculative repeated Actions edit loop.

## Executed supporting tests and artifacts

Two new test scripts are committed; their existing #322 reference dependency
is unchanged. Thirteen small original-H models compare all 554 square active
systems (264 nonsingular) with 103 actual vertices and 181 edges. The 721 routes
contain 1224 original-edge occurrences versus 1168 shortest edges: all 56
nonshortest outputs remain. Tests include nonsimple and lower-dimensional bases,
signed roof coefficients, a 2^-80 height margin and zero dimensions.

Four growing-roof cases (n,k)=(4,4),(8,8),(16,16),(32,32) certify 120 further
original edges on 16/32/64/128 rows. The 64D case has 32 exceptional roof rows
and a checked 64-edge route. Its 4,294,967,297 levels per exceptional row and
2^64 total vertices are WRITTEN formula evaluations, not graph enumeration or
separate Lean theorems. Sparse original-row right inverses check rank and whole
support segments. Saved replay disables production. Nine malformed controls
are rejected; zero-height label collapse remains a structural boundary example.

A clean three-script workspace reproduces all five full reports/fixtures exactly.
The 184868-byte small fixture and 2361480-byte large fixture accompany the export;
committed summaries bind them by hash and the scripts regenerate them. Python
and JSON are not kernel-verified. These tests are not Lean compilation.

Only request artifact 10671893408 was produced: 307 bytes, SHA256
50bb976c6d2a0483b2a496a532f38da5ab4b50a562b46e2ba08e1556cddca110.
It was downloaded and rehashed; its unchanged resolved.json is preserved.
No missing verified or publication artifact is invented. Derived source, test,
repair and run records are labelled separately from the request and diagnostics.

    python3 scripts/test_affine_roof_routes.py --out /tmp/roofs --stage small
    python3 scripts/test_affine_roof_routes.py --out /tmp/roofs --stage controls
    python3 scripts/test_affine_roof_large.py --out /tmp/roofs

## Exact next step and ownership

Resume THIS PR and its saved repair after reading the five project instructions
and current live heads/comments/reviews. Check for later ownership, pending runs
or accepted results before any write. Apply/review the two-file proposal and
compile locally if available, then use one complete prepared pinned final gate.
Keep the original failed inputs and evidence. Do not rename an overlapping target.

Coordination on #325: 5769527466, posted/read back. Its separately owned general
few-exception proof and repairs were not changed or triggered. #282's triangular
work, reserved #210 and all other owners' branches are untouched. Local Lean/Lake
were not found on PATH or in checked home/opt locations and toolchain-host DNS
failed. Lean 4.30.0 / Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f, strict
0.10.7 publication compatibility and verifier/publisher secret isolation are unchanged.
