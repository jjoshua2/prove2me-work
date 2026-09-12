# Recursive product verification

Original #204 source `55edf3dee8f80685fe100467f57f4b95b20c9b5a` compiles unchanged
against merged #203. Final source `fcbb02425dececaa9a8f7abd90c341ae99dbafac`
extracts the geometric predicate into its public definition and updates the
regression receipt's hash scope. No routing argument or discovery code changed.

`local-build.log` and `local-audit.json`: targeted build PASS; seven required
declarations and 272 reports across dependencies, standard logical axioms only.
`rational-check.json`: fresh full regression PASS, 32 positive certificates,
120 independently enumerated positive-case vertices, 256 edges, 2,720 ordered
vertex-pair distances, 32 source-target vertex maps, and 15 negative controls.
Original test receipts remain unchanged. The checker is an exact rational
verifier, not a Lean proof-term generator.

The final hosted gate 34712133611 on fcbb024 is SUCCESS; its axiom audit passes
the same seven required declarations and 272 reports. Run 34712025298 selected
stale 55edf3d immediately after a push and was cancelled; it supplies no evidence.
The separate publication packet contains a standalone explicit-premise driver,
its standard-axiom audit and the exact public theorem composition.

`feedback-box-check.json` covers the subsequent paper proof (not Lean):
12 cyclic/dense/weighted-dense examples, 180 vertices, 384 exact edges, 4,080
ordered coordinate-toggle routes and four rejected invalid finite witnesses.
This new regression and paper note were added after the frozen Lean source;
they are not attributed to the hosted Lean gate or platform theorem.
