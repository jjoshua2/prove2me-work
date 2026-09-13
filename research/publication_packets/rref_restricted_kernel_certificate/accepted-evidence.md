# Accepted evidence — RREF basis certificate for a one-ray restricted kernel

The corrected standalone packet and matching module were compiled and axiom-audited by the trusted comment gate, then submitted by the trusted publisher.

- Theorem: `Hirsch.rref_basis_certificate_restricted_kernel_one_ray`
- Theorem ID: `4a5d83c2-d0fa-4e24-93b2-29bb39eb55e8`
- Submission ID: `de82dc98-0819-4305-968d-cff93ef9ada6`
- Authenticated verdict: `ACCEPTED`
- Audited proof head: `eccaa867db05fd19caf84096697f77a146eb7977`
- GitHub Actions run: `34785831366`
- Authenticated verdict comment: `https://github.com/jjoshua2/prove2me-work/pull/230#issuecomment-5656510253`

The first gate stopped during Lean compilation before theorem registration; its sole remaining goal was scalar commutativity. The corrected packet changes only that closing simplification and preserves the theorem statement and assumptions.

The theorem certifies that finitely checked row-combination identities on the standard coordinate columns force every signed null vector supported inside the candidate support to be a scalar multiple of the candidate. It does not prove that a particular imperative RREF implementation emitted the certificate honestly, positivity/minimality of the candidate, or any Hirsch diameter bound.

Do not resubmit this theorem or packet under the same name.
