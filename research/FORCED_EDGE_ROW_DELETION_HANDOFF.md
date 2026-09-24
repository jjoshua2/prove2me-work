# PR344: forced-edge row deletion is ACCEPTED

Read current main, project instructions, live PR lifecycle and ownership first.
Do not reapply the scalar repair, repeat protocol maintenance or resubmit this
theorem. Respect #326/#282, reserved #210 and other live assignments.

Target: Hirsch.forced_original_edges_survive_row_deletion.
Packet: research/publication_packets/forced_edge_row_deletion.
Branch: proof/forced-edge-row-deletion.
Frozen accepted proof:f9a606ff784dc8882473ac6e8cd9d80e548d2d38.
Theorem:ee659ed9-1c3d-4169-acf8-f1db5af75838.
Submission:a12c4ef6-e7d4-48ce-af5e-7cb1059ae5fb.
Request5818926132; acknowledgement5818929044; run36034487100;
verdict5818997831 at2026-09-24T17:32:56Z.
The raw receipt records PUBLISHED/ACCEPTED/Proved; Proved is the trusted
publisher's authenticated readback, not an independent fresh platform poll.

All three compiler stages pass; all five reports in both proof logs are
standard-only. Source382 lines/16120 bytes, blob387280cd1b07c65480a4fefa34148c24a15c5aed,
SHA256727f300d80bb3cd09147d7ca46810a2a066e99a48c5a52705e63c1559f1914fd.
The final proof change was only rfl after the scalar simplification. Public
root, accepted helpers, metadata and explanation remain frozen.

The first run36013003665 failed compilation. Run36031864783 passed compilation
but stopped at the old protocol guard. Separately reviewed maintenance #345
merged as10468186f549e7aece26b923a2c9342b22c42944; it retains exact-version rejection
at0.11.0. The successful operational resume uses the SAME frozen proof. These
are three compiler gates and one actual platform proof submission, not three
submissions. No licensing status/acceptance call was made. Earlier-contribution
license grants require explicit owner authorization; do not infer it here.

## Mathematical result and next obligation

Hall-forced original edges lift to exposed line sections of the relaxation
retaining target-tight rows plus J. Intersection with the original P recovers
each old edge exactly, so distinct geometric edges cannot merge. The common-
active affine line and summed-row exposing functional are derived. Old endpoints
may disappear as relaxed vertices and extensions may be rays. No boundedness,
full dimension, finite-hull representation or vertex catalogue is required.

The forced-label hypothesis selects edges; it is not a small-carrier-count
assumption. Repeated occurrences are not made distinct. No polynomial congestion
or original-route construction follows merely from this injection. Select a
specific unowned positive obligation controlling these carriers along a chosen
original ordinary-edge route. Do not replace the missing bound by a new premise
or count all auxiliary carriers as though that solved the original mission.

## Evidence and reproduction

Current packet:accepted-evidence.md and publication-receipt.json.
Raw successful files:research/verification/forced-edge-row-deletion/accepted-run/raw/.
Raw protocol stop:research/verification/forced-edge-row-deletion/protocol-stop/raw/.
Original first-attempt/ remains unchanged. The previous handoff is preserved
under accepted-run/previous-handoff.md. Check current PR metadata for integration.

    python3 scripts/test_row_deletion_edges.py --out /tmp/deletion-small
    python3 scripts/test_row_deletion_edges.py --large --out /tmp/deletion-large

Both unchanged suites reran with four byte-identical outputs:7638 small carriers,
62212 probes,116 selected high-dimensional carriers and812 probes;8 controls.
Python/JSON and offline archive checks are not kernel-verified. Complete outputs,
all successful original ZIPs, protocol history and the initial failure archive
accompany the export. No local Lean run or full raw runner archive is claimed.

Preserve Lean4.30.0/Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f, strict reviewed
0.11.0, accepted inputs, duplicate guards and verifier/publisher secret separation.
