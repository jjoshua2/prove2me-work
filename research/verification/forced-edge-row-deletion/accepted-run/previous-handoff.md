# PR344: forced-edge deletion — one scalar identity remains

Read the current five project instructions, live main, PR head/comments and
ownership before continuing. Resume this SAME target; respect #326/#282,
reserved #210 and all other active claims. Do not redo accepted #343.

Branch: proof/forced-edge-row-deletion.
Packet: research/publication_packets/forced_edge_row_deletion.
Target: Hirsch.forced_original_edges_survive_row_deletion.
Tested proof:d85aea5893d68d54bff16a9c86832cceded1f336.
Source381 lines/16108 bytes, blob9755f146f1739e60ec5ba7c642804f7a63f73f53,
SHA25640a73f82531077c56a451d07836ad79a612fff4bc693ac46ad26b606627ca4dd.
Main at gate:60fce04c2cb45b7e1f9087b9ebd8630f16c1f051.

Coordination5815792776; request5816084645; acknowledgement5816088496;
run36013003665. Gate107678228843 passed; verify107678296812 failed at199:19.
Publish107678827440/report107678827174 skipped. Standalone solution/statement
not reached. One hosted attempt; no registration, actual proof submission,
IDs, verified artifact, receipt, ACCEPTED or Proved. No second trigger.

## Exact next proof action

Apply first-attempt/proposed-scalar-identity-repair.patch. In map_smul' for the
sum of common-active rows, keep the existing simp only and append rfl before
its closing brace. The reported goal differs only by (RingHom.id R) c versus c.
The proposal adds one proof line, preserving every declaration signature,
accepted helper, complete public root statement/proof and metadata file.

Proposed382 lines/16120 bytes, computed blob
387280cd1b07c65480a4fefa34148c24a15c5aed, SHA256
727f300d80bb3cd09147d7ca46810a2a066e99a48c5a52705e63c1559f1914fd.
This is UNAPPLIED and UNCOMPILED. Apply/reverse checks pass, not Lean. Further
errors may appear. Recheck live pending/ownership state, apply exactly, compile
locally when available, then use one prepared complete pinned gate. Never
weaken the target or rename it to get around this local proof error.

## Verified helpers and mathematical boundary

active_kernel_direction and active_equations_iff_line have standard-only
reports. They derive the common-active kernel and affine line of an actual
original exposed edge, without a full-dimensionality or rank premise.
common_slice_exposed, retained_edge_extension and solution retain failed-
elaboration sorryAx. No admission was written; the whole packet is not verified.

The complete candidate lifts Hall-forced original edges to exposed affine-line
sections of the relaxation keeping target-tight rows plus J. Reinsertion
recovers each original edge exactly, giving nonmerging of distinct geometric
edges. Old endpoints may cease to be vertices and extensions may be rays.
The condition S_e subset J specifies forced edges, not a small-congestion bound.
No polynomial carrier count or original-route construction is concluded.

## Reproduction and stored evidence

    python3 scripts/test_row_deletion_edges.py --out /tmp/deletion-small
    python3 scripts/test_row_deletion_edges.py --large --out /tmp/deletion-large

The new script imports the unchanged committed PR343 test_optimal_row_charging.py,
not the previously blocked script. Nine small models:7638 carriers/62212 probes,
3268 rays,3285 enlargements,3290 lost endpoints;8 rejected controls. Four selected
8/16/32/64D models add116 carriers/812 probes, not complete graphs. All four full
outputs match a clean two-script replay. Python/JSON are not kernel-verified.

Packet first-gate-evidence.md and research/verification/forced-edge-row-deletion/
first-attempt/ preserve exact failed inputs, full displayed error/five reports,
raw resolved request, proposed patch and labelled derived readbacks. The export
includes the original request ZIP, full proposed source, complete fixtures and
both runnable scripts. Only request artifact10812524834 exists,307 bytes,
SHA2563553ac8c499aeb674324d737b52a70b63ba398dcb51dab26a24dad33f633db91.
Diagnostic excerpts are not full raw runner archives; no publication receipt
exists. Local compiler/cache absent, toolchain DNS failed. Retain Lean4.30.0,
Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.9 and all safeguards.
