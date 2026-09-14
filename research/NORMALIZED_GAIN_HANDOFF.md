# Resume route-length research without duplicating accepted edge-validity work

Read live STATUS and the current PR queue. #248's normalized-tangent-to-edge
result is accepted/merged. #244 retains its separate supplied-core assembly.
This contribution changes neither source nor theorem and requests no hosted
Lean workflow. It adds a research proof, exact original-H pivot auditor,
classical greatest-improvement comparator, regression and reproducible fixtures.

Main result: on an explicit capped Klee--Minty d-polytope with 2d+1 GENUINE
original facets and endpoints sharing no facet, canonical-active-row normalized
derivative takes floor(2^(d+1)/3)+1 edges. A d+1 path exists in all dimensions;
the full-gain comparator returns shortest d-step routes in every tested d2..12.
All-d derivation and exact boundary to #248's default witness choices are in
NORMALIZED_GAIN_FULL_FACE_BARRIER.md. The default #248 discover_vertex/ExactLP
selection has NOT been replayed; do not turn this into an unsupported claim
about that exact implementation. It is a lower bound for a legal canonical
height policy and a refutation of a bound from the broad invariants alone.

Run python3 scripts/test_normalized_gain_barrier.py. It creates the d2..5 full
trace/input fixtures; large dimensions are summary-only. The independent audit
has no inverse, LP or rank search. SymPy is used for the d2..4 reference graphs.
Source hashes and exact counts are in NORMALIZED_GAIN_BARRIER_TESTS.json.
These tests are not Lean verification, and no mathematical proof packet is
being published. An uncompiled skeleton is not useful and has not been added.

Next useful experiment: replay the exact #248 default solver on the committed
inputs and compare its derived heights/objectives with this canonical policy.
Then test target-aware or completed-step portfolios on additional non-product,
non-redundant original-H instances. Changes to a height or objective can matter;
log the actual coefficients and certified original edge count. Count LP work
separately from graph steps. Do not claim a global guarantee from defeating
Klee--Minty, or from any finite collection of short routes.

This is ready-to-run research code and a written theorem/counterexample to an
algorithmic shortcut. Generic code and the all-d geometric argument have not
been compiled in Lean or accepted by Prove2Me. No security, workflow or pin
changes are needed, and no accepted or pending packet should be resubmitted.
