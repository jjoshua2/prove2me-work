# Delivery and verification handoff

The mathematical note, three Lean candidates, executed test receipts and
numerical fixtures are preserved in this branch. GitHub tool calls uploading
the Python checker sources were blocked with an undetermined safety-status
error. Those four sources were not committed; they remain in the complete
conversation ZIP packet linked with this continuation.

The packet contains these reproducibility sources:

- scripts/positive_feedback_box_certificate.py
- scripts/test_positive_feedback_boxes.py
- scripts/positive_box_monotone_cut.py
- scripts/test_positive_box_monotone_cut.py

Their exact SHA-256 values are in COUPLED_BOX_CHECK_2026-09-12.json alongside
the tested Lean source hashes. Repository-only checkout does not yet contain
those four scripts. The reproduction commands in the note require the packet.
No test count is inferred from an unexecuted check: both suites ran locally.

The three Lean modules now pass local Lean 4.30.0 compilation after
elaboration and scalar-arithmetic repairs, with unchanged theorem hypotheses.
All twelve printed declarations have only `propext`, `Classical.choice`, and
`Quot.sound` transitively. See
[the current audit](verification/2026-09-12-coupled-boxes/local-audit.json).
The core d-edge theorem has no small-excess or Larman premise.

The original four Python files were not available in this checkout during
integration. Their historical test counts above were not rerun. The independent
`python3 scripts/verify_coupled_box_fixtures.py` verifies the committed fixtures:
two normal forms, thirteen route vertices, eleven actual ordinary edges,
thirty-two common-face vertices, and four invalid-certificate controls.
[New receipt](verification/2026-09-12-coupled-boxes/fixture-check.json).
This verifies the supplied examples; it does not recover the missing original
checker implementation or formally prove the Schur and monotone-cut claims.

Formalization scope is deliberately limited: core vertex classification,
one-bit ordinary edges, the d upper bound, and the same-selected-pair carrier
adapter. The reverse-edge/Hamming lower bound, infinite cyclic separator
obstruction, Schur closure and monotone-cut theorems have mathematical proofs
and specified finite tests, not new Lean declarations. The q>1 cut consequence
is mathematical only; only the one-cut router is implemented.

Platform acceptance and final hosted verification are recorded separately
when completed; local compilation alone is not platform acceptance.

Final hosted run [34723396993](https://github.com/jjoshua2/prove2me-work/actions/runs/34723396993)
succeeded at `163caecb77418e3bd998e0b225f8685d45dc7139`; its twelve required
axiom reports also pass. The exact standalone matrix theorem is registered as
[4096cd8a](https://prove2.me/theorems/4096cd8a-6bf6-4788-89be-e67f84f6c92f).
Submission `05df606c-7c8c-42eb-9e69-794b6be48926` is pending at this integration
checkpoint; this is not yet an acceptance claim. Poll the existing submission
with `scripts/publish_self_contained_packet.py` and preserve its verdict.

**Final platform verdict:** submission `05df606c-7c8c-42eb-9e69-794b6be48926`
is ACCEPTED. Authenticated readback says Proved and its exact accepted source
matches the frozen solution. Receipts are in
`publication_packets/positive_feedback_boxes/`. PR #205 is merged.
