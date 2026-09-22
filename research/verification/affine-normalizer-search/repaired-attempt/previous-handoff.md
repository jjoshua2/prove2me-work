# PR #334: complete affine-normalizer search — one first-gate API error

Read the five project instruction files and LIVE heads/comments before resuming.
#333 is accepted/merged, not to be resubmitted. #326/#282 and reserved #210 remain
other-owned. This continuation owns the finite normalizer-synthesis obligation.
Keep #334 open/draft: no complete passing packet or platform submission exists.

## Exact identity and command

Repository jjoshua2/prove2me-work; PR #334.
Branch proof/affine-normalizer-search.
Target Hirsch.affine_normalizer_finite_search.
Packet research/publication_packets/affine_normalizer_search.
Tested proof a3ac7e377ae4a5a902108989f42e0b215214b1dd.
Main/base/trusted publisher165eadd7cfc012c6d251b576ee89351c8fea8b62.
Solution262 lines/11791 bytes, blobbe277e04acf17243362c513c6a54b097cf8f3d55,
SHA256146184c2ffbe787c11e85db3ac572a4b2603aad544fe81799996701158edda7c.
Problem8095b41efacbedd21a33ba58468b4ee1f791e3d1; explanation10d80530164e362915fc76db9c03a11befc69d16.
Later supporting heads do not replace the tested proof identity.

Coordination5781110223 on #333; actual NEW top-level request5781315324;
acknowledgement5781318502; run35763480309. All were posted/read back as applicable.
Gate106867036774 passed; verify106867129911 failed driver compilation with exit1.
Publish106867576094 and report-verify106867576462 skipped. Separate solution and
statement compiles were not reached. One hosted attempt, zero actual platform
registrations/submissions; no theorem/submission ID, ACCEPTED or Proved exists.

## Error and precise saved proposal

One error at141:8: unknown constant Finset.card_le_card_of_surjective.
Three named reports are standard-only: compress_tests, compress_ties and anchor.
image_card_of_ties, catalogue and public solution retain failed-elaboration
sorryAx. No admission was written; clean tie compression is not a verified
complete optimum theorem. The other messages are harmless tactic warnings.

The pinned file Mathlib/Data/Fintype/Card.lean was read at the unchanged revision
and confirms Fintype.card_le_of_surjective (f) (h). Its native blob is
92b0c19123219c529f84acd7a7db084b2bb3b886. The failed Finset API name was from
newer documentation. Repair the API use; never upgrade the pin to obtain it.

UNAPPLIED and UNCOMPILED patch:
research/verification/affine-normalizer-search/first-attempt/proposed-cardinality-repair.patch.
Replace only the last line of image_card_of_ties with:

    have hc := Fintype.card_le_of_surjective F hsurj
    simpa only [Fintype.card_coe] using hc

All signatures, hypotheses, other proof code, the complete public type and its
assembly, metadata and explanation stay unchanged. Apply/check/reverse passes.
Proposed source263 lines/11835 bytes, blobe7b359fae3953d789c936217ce730b7139e361d5,
SHA2565e37a3c417a051e978bf7cb6f330007eb27a0808dc0530f02ee30c449e1e233c.
Full proposed source is exported; repository stores the exact patch.
Further errors may appear. Recheck pending work, apply this narrow patch,
compile locally when available, then use one prepared complete final gate on
THIS same target/PR. Preserve the first failure. No second trigger was posted.

## Mathematics and next mission gap

Inputs: finite C in R^d, arbitrary scalar numerator s, and anchor u in C.
No denominator, equality partition, basis, rank or small spectrum is assumed.
Anchoring q by q(u)>0 leaves d slope variables. A tie is the linear equation

    D(s(x)*(y-u)-s(y)*(x-u)) = s(y)-s(x).

Derive at most d original pair tests spanning every tie of any positive slope.
Any positive solution of those tests retains all old ties and may merge more.
Choose one positive feasible solution per at-most-d subsystem, or constant one
for an infeasible subsystem. This fixed finite family covers ALL positive real
affine denominators. Minimizing its finite spectrum returns an attained global
optimum. The hard tie-compression and anchor parts have clean reports; the
finite-cardinality wrapper blocks full verification.

The public Lean result is finite completeness/existence via classical choice,
not an extracted strict-LP program. Written composition with accepted #333
synthesizes each original row independently then selects its determining budget.
That application requires C to be the COMPLETE actual vertex set and exact
original H/hull equality. Samples or visited vertices are not substitutes.
The catalogue can be exponential in d; the actual vertex inventory can be
exponential in original facets. No uniform small optimum, polynomial-time
original-H algorithm, H-to-V method, shortestness or Polynomial Hirsch result.
This is not #204's old product-chart recognition or another raw-measure barrier.

## Exact software and durable evidence

normalizer_synthesis.py performs rational equality elimination and STRICT
Fourier--Motzkin. It outputs positive slopes or exact equality/positivity dual
exclusions. A separate consumer checks original equations and strict positivity,
full kernels via independent SymPy rank, duals and exhaustive basis coverage.
Early termination requires the universal sign-class lower bound. Caps raise
NOT-an-exclusion/optimum errors. Python and JSON parsing are not verified.

20 original-H hulls/136 rows:1300 systems,613 positive,687 excluded;31 exhaustive
rows,24 improved spectra. All721 ordered endpoint routes produce867 original
edges versus862 shortest edges;4 nonshortest retained. Five more finite-data
cases check26 systems; signed,zero,collinear and2^-80 data included. Ten malformed
controls fail. Saved replay disables synthesis/elimination/feasibility/route/edge
producers. A clean five-script workspace reproduces full report and fixtures.

    python3 scripts/test_normalizer_synthesis.py --out /tmp/normalizer-results

The two new scripts and three unchanged prior scripts are in the export.
Only the two new scripts are added to the repository. Prior three native-main
blob readbacks match. Complete JSON outputs are exported/regenerate; repository
summaries are labelled derived, not raw Lean or platform results.

Only request artifact10710478576 exists:308 bytes, rehashed SHA256
3ef84dd2592bd28f74f078835db31c17668c5a0e89cf7c0f5030735d652e4e48.
The exact request, original failed inputs, selected compiler diagnostics/all6
reports, selected runner lines, pinned-API readback and proposal are preserved.
Full decoded runner log was read through cleanup; excerpts are not a full raw
archive. No absent verification artifact or receipt is fabricated.

Retain Lean4.30.0/Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f and strict0.10.8.
Local lean/lake/elan/caches absent and toolchain hosts fail DNS; source/Python
checks were not local compilation. Accepted inputs, other owners, actor allowlist,
duplicate guards and verifier/publisher credential separation remain unchanged.
