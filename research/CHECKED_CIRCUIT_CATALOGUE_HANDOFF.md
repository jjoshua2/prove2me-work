# Exact executable circuit-catalogue audit

PR #229 is distinct from #227 support-budget composition and from the integrated
#225/#226 routing cores. #222 proves the rank cutoff; #224's geometric vertex
characterization is now ACCEPTED and merged. The new packet reuses #222's
signed-ray and rank helper proofs verbatim, with no target import or axiom.

Packet: research/publication_packets/checked_circuit_catalogue/.
Source proof head: af2d89387f1fb0058e5eb17d4c3762a5b93208c4.
Initial final gate:34785381971. Read its actual outcome; this handoff does not
claim compilation or acceptance before the returned evidence exists.

For each support of size<=k+1 the Boolean checker verifies either a rational
left inverse of [A_S;ones] or a nonzero supported zero-mass null witness. It
then emits only strictly positive, normalized original null vectors. The new
theorem proves this returned catalogue includes ALL normalized REAL circuits,
not merely that each returned vector is valid. No arbitrary omitted support
is trusted; every support has a checked exclusion or reconstruction identity.

The producer can use untrusted RREF. The audit does not, and the executable
Lean checker can independently consume the finite exported rational data.
The source has three kernel decide examples. Python and JSON decoding are
NOT thereby verified or extracted; a future pipeline should generate a Lean
certificate file and apply the theorem to its checked table.

Reproduce the exact companion test using:

    python3 scripts/test_checked_circuit_catalogue.py

Generate a table from JSON {A,n} using:

    python3 scripts/checked_circuit_catalogue.py input.json --output table.json

The committed receipt records55 small systems,1633 independent all-support
reference checks, and17 rejected forgeries. The large n32/k2 case checks5489
supports and returns886 circuits, not all2^32 supports. Enumeration is only
polynomial for fixed k; no general polynomial runtime or bit bound is claimed.
The zero-map n64 example is a boundary case, not evidence for difficult large k.

The original container had no local Lean/Lake. Source checks and Python are
not compilation. Only actual compile logs, axiom audit and authenticated
platform verdict can upgrade the corresponding status. If a proof error is
found, preserve exact diagnostics and repair locally without weakening the
statement; do not make Actions a speculative edit/compile loop.

After acceptance, integrate the exact packet and receipts, not the old #210
research ancestry. The remaining root issue is arbitrary-carrier routing and
useful geometric decomposition. This catalogue verifier does not solve it.
