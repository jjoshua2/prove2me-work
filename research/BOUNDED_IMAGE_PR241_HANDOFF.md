# PR #241: committed candidate, blocked publication trigger, exact edge stress test

## Actual state

Mathematical proof head: 90f7d8a7acd078558e18df0737d20014ef80b0e5.
Packet: research/publication_packets/bounded_image_representatives/.
The 398-line solution, statement and explanation match the earlier prepared
candidate exactly. The actual publication-comment tool call was blocked before
creation. The following PR comment readback was empty. No workflow was triggered,
no theorem registered, and no proof compiled or submitted. Keep the PR draft.
No alternative trigger was used. This is not evidence of a workflow defect or a
reason to change permissions, the allowlist, the pin or the secret split.

Local Lean/Lake is unavailable. Exact rational/source tests are not compilation.
The next verification agent should compile the unchanged packet under Lean4.30.0
and Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f, audit its five declarations,
and only then finish the normal authorized publication cycle. Preserve failures
and exact source hashes. Do not import the target as its own proof.

## What is added after the proof head

scripts/test_projection_edge_gap.py and its source-hashed execution receipt
implement an exact original-row sufficient certificate for a true image edge.
research/COMPACT_MODELS_AND_ORIGINAL_EDGES.md explains the theorem and uses a
classical Klee--Minty shadow to stress-test it. This is mathematical/computational
review of the genuine remaining graph-transport issue, not a new Lean theorem.
The original four proof packet files are not modified by this addition.

Through d12 the independent hull check reconstructs the complete image graph:
8188 vertex certificates,45056 original edges,8188 true projected edges,36868
projected chords. Eight forged cases fail. Above d12 only33 selected vertex
certificates are tested. Huge counts/distances there come from the classical
construction, never a claimed enumeration. The image facet count is2^d, not2d.

The decisive distinction is that a compact easy extension and a vertex bijection
can still send a two-edge path to a chord needing exponentially many image edges.
The pending bounded-representative result cannot itself transport diameter. Its
same-cap face-image corollary is useful but also insufficient for short routes.
Use #239/#240's already-accepted genuine Minkowski bridge structure or a proved
original-row supporting-face condition, not image equality alone.

## Reproduction and boundaries

    python3 scripts/test_projection_edge_gap.py

This script writes research/PROJECTION_EDGE_GAP_TESTS.json and regenerates the
complete d8 worked fixture in fixtures/projection_edge_gap_example.json. It
uses Python Fraction exact arithmetic and an independent planar hull. It is
not Lean-extracted or kernel-certified. Its --max-dimension cap is explicit.
The older representative constructor/test and its execution receipt remain in
the complete conversation bundle; this handoff does not claim that old script
was uploaded in this follow-up. Run it there using:

    python3 scripts/test_bounded_representatives.py

No new ordinary-edge upper bound for arbitrary carriers or proof of Polynomial
Hirsch is asserted. The hard remaining problem is a short sequence of correctly
certified image/original edges with a budget in the ORIGINAL facet count.
Do not duplicate #238 support-witness work or the accepted #239/#240 bridges.
