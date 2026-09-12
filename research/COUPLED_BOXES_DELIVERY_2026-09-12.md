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

The three NEW Lean modules have not been compiled. The next local gate is:

    lake build Solutions.PolynomialPairedBasisRouting
    lake build Solutions.PolynomialPositiveFeedbackBoxes
    lake build Solutions.PolynomialCoupledBoxCarrierRouting

Audit all twelve printed declarations with the usual standard axioms only.
No small-excess or Larman premise is needed by the core d-edge theorem.
#203 is a dependency of the image adapter, but #204 is not a dependency.

Formalization scope is deliberately limited: core vertex classification,
one-bit ordinary edges, the d upper bound, and the same-selected-pair carrier
adapter. The reverse-edge/Hamming lower bound, infinite cyclic separator
obstruction, Schur closure and monotone-cut theorems have mathematical proofs
and specified finite tests, not new Lean declarations. The q>1 cut consequence
is mathematical only; only the one-cut router is implemented.

Keep the PR draft until this new-module gate passes. Do not treat a rational
certificate, finite test, or uncompiled proof as a platform acceptance record.
