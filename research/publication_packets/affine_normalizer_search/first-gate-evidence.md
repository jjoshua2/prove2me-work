# First gate: tie compression clean; one pinned-API repair remains

This is failure evidence, not a publication receipt. PR #334 stays open/draft.
Target Hirsch.affine_normalizer_finite_search.
Tested proof a3ac7e377ae4a5a902108989f42e0b215214b1dd.
Source262 lines/11791 bytes, blobbe277e04acf17243362c513c6a54b097cf8f3d55,
SHA256146184c2ffbe787c11e85db3ac572a4b2603aad544fe81799996701158edda7c.
No source, public type or metadata changed after the gate.

Actual new top-level request5781315324 and acknowledgement5781318502 resolve
run35763480309 to that exact proof. Both were read back. Gate106867036774 passed;
verifier106867129911 failed driver compilation at141:8: unknown constant
Finset.card_le_card_of_surjective. Standalone solution and separate statement
compiles were not reached. Publish106867576094 and report106867576462 skipped.
No complete verified artifact, theorem registration, proof submission, IDs,
ACCEPTED or Proved result occurred. One hosted attempt; no second trigger.

Three named reports are standard-only: compress_tests, compress_ties and anchor.
They establish the at-most-d original tie-equation compression and anchor
normalization. image_card_of_ties, catalogue and public solution still include
failed-elaboration sorryAx. No admission was written, but the complete global
optimum theorem is NOT yet verified. Harmless tactic warnings are retained.

The proposed single-site replacement is:

    have hc := Fintype.card_le_of_surjective F hsurj
    simpa only [Fintype.card_coe] using hc

The pinned Mathlib/Data/Fintype/Card.lean was read directly at
c5ea00351c28e24afc9f0f84379aa41082b1188f; blob92b0c19123219c529f84acd7a7db084b2bb3b886
contains that Fintype lemma. The candidate's Finset spelling had been found in
newer documentation, not this pin. Do not upgrade the environment.

The patch is saved UNAPPLIED and UNCOMPILED in
research/verification/affine-normalizer-search/first-attempt/proposed-cardinality-repair.patch.
It changes only the last line of image_card_of_ties into the two lines above.
All signatures, other proofs, public statement, metadata and explanation remain
unchanged. Apply/check/reverse succeeds, not Lean verification. Proposed source:
263 lines/11835 bytes, blobe7b359fae3953d789c936217ce730b7139e361d5,
SHA2565e37a3c417a051e978bf7cb6f330007eb27a0808dc0530f02ee30c449e1e233c.
Further errors may appear. Resume this same PR after live ownership/pending checks.

The complete written argument constructs a finite family of positive affine
normalizers covering every competitor's ratio ties and attaining the global
minimum spectrum. Only finite C, scalar s and anchor u in C are inputs. The
formal Lean construction uses classical choice; the rational implementation
is separate. Search remains potentially exponential in dimension and in a
vertex inventory which itself need not be polynomial in original facets.
No universally small optimum, efficient H-to-V or Polynomial Hirsch claim.
Original-route application with accepted #333 is written/tested, not a new
formal route theorem; it requires the complete actual vertex set and H/hull equality.

Executed exact search:20 hulls/136 original rows,1300 systems,613 feasible and687
excluded;31 exhaustive rows and24 reduced spectra. Synthesized denominators
support721 routes/867 original edges versus862 shortest edges; all4 nonshortest
routes remain. Five further finite-data cases check26 systems. Ten malformed
controls fail. A clean five-script replay reproduces full13220-byte report and
2259497-byte fixtures exactly. Three reused geometry scripts match native main
blob readbacks. Tests verify exact witnesses/dual exclusions, not Python/JSON
correctness or an all-real theorem by sampling.

Only raw request artifact10710478576 was produced:308 bytes, downloaded and
rehashed SHA2563ef84dd2592bd28f74f078835db31c17668c5a0e89cf7c0f5030735d652e4e48.
Its exact resolved request is preserved. Failed packet inputs, all six reports,
selected actual compiler diagnostics, pinned-API excerpt and patch are retained.
The full decoded runner log was read through cleanup; stored excerpts are NOT
a complete raw runner archive. No missing verified/publication artifact is invented.

Durable handoff: research/AFFINE_NORMALIZER_SEARCH_HANDOFF.md. Keep this PR draft.
Local Lean/Lake/Elan and checked caches were absent; toolchain-host DNS failed.
Hosted Lean4.30.0 was observed; retain its Mathlib pin and strict protocol0.10.8.
#326,#282,reserved #210, accepted dependencies and publication safeguards untouched.
