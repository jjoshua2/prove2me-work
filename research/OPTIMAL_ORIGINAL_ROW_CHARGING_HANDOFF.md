# PR343: optimal original-row charging is ACCEPTED

Read live main, current instructions, ownership and PR lifecycle before continuing.
Do not reapply either saved repair or resubmit this accepted theorem. Respect
#326, #282, reserved #210 and all other live assignments.

Target: Hirsch.optimal_original_row_edge_charging.
Packet: research/publication_packets/optimal_original_row_charging.
Branch: proof/optimal-original-row-charging.
Accepted proof:0568508f461b614fd0a6f7a6bad5decee1e2a540.
Theorem:c686867d-29b6-4c57-a9fa-59852b51c051.
Submission:98759442-081e-4d9a-b0b6-f59cf4f51140.
Request5815351636; acknowledgement5815355645; run36008100463;
accepted verdict5815455088 at2026-09-24T13:53:43Z.
The raw receipt records PUBLISHED/ACCEPTED/Proved. Proved is the trusted
publisher's authenticated readback, not an independent fresh platform poll.

All three compiler stages pass. All five reports in both complete proof logs
use only propext, Classical.choice and Quot.sound. Third hosted attempt, first
actual platform proof submission. The source is356 lines/14549 bytes, blob
87d719f1cde8a87c29a90cfd7d6bfec4801ce7e7, SHA256
d3228b6e74e04152953b153a5859a02b24d16bb4a7054ba874bc340133a03c76.
The final change replaced one unavailable lemma call with simpa using hiJ.
All other proof text, complete public root and metadata are unchanged.

## Mathematics and next obligation

For a GIVEN finite family of genuine non-target original exposed-edge occurrences,
the theorem derives eligible original rows, an assignment with optimal maximum
load K, the exact forced-row capacity criterion and a nonempty overloaded row
subset for every k<K. Capacity k is feasible iff |F(J)|<=k*|J| for all J subset I,
where F(J) contains occurrences whose entire eligible set lies in J.

No route is constructed and no polynomial bound on K is assumed or concluded.
Occurrences may repeat; dimension is arbitrary and the H-body need not be bounded.
Actual target/endpoint extremality and whole nondegenerate original exposed edges
remain explicit. Target-incident terminal edges require separate accounting.
The next positive geometric task is deriving controlled forced-row density along
a constructed original ordinary-edge route. Do not replace that task with another
equivalent matching wrapper or a new favorable-load assumption. Inspect current
research handoffs and counterexamples before choosing a distinct unowned task.

## Evidence and reproduction

Current packet note:accepted-evidence.md; exact verdict:publication-receipt.json.
Successful original files:research/verification/optimal-original-row-charging/
accepted-run/raw/. Combined15-file raw tree:
e99b541ba9800c4755cea626079495fa2e4bedcc, independently rehashed.
Both prior failed runs35998089588 and36003244581, their inputs and diagnostics
remain in first-attempt/ and second-attempt/. Previous-handoff.md in accepted-run/
retains the last failed state. Those old notes are not current blockers.

    python3 scripts/test_optimal_row_charging.py --out /tmp/charging-small
    python3 scripts/test_optimal_row_charging.py --large --out /tmp/charging-large

Both unchanged suites reran and all four complete outputs match prior bytes.
2928 finite families/22968 assignments,67 ledgers/1269 occurrences and9 controls.
Selected64D examples are not full graphs; the Gray detour is not a diameter lower
bound. Python/JSON and offline archive checks are not kernel-verified.

The export contains original successful ZIPs, both prior failure histories,
complete fresh tests and a checker. Local Lean/cache was absent and toolchain
DNS failed; actual verification is hosted. No full runner archive, individual
platform API bodies or independent mission-root poll is claimed. Preserve
Lean4.30.0/Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.9,
accepted inputs, duplicate guards and verifier/publisher isolation. Check live
PR metadata for the actual merge identity; no further publication is needed.
