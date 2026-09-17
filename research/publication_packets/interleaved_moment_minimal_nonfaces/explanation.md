# Interleaving identifies the actual minimal nonfaces

The accepted #286 theorem constructs barycentric weights and finds a strictly slack row on each weight-sign side. It did not identify those signs for a desired ordered family. This packet proves that identification and combines it with #285 to establish minimality. It does not submit either accepted theorem again.

Index the selected nodes by pairs (i,b). The order assumptions put l_i<r_i<l_j<r_j whenever i<j. In the barycentric denominator at a node in pair i, group every other pair j into (x-r_j)(x-l_j). This is strictly positive: both factors have the same nonzero sign. The remaining partner factor is negative at l_i and positive at r_i. Taking reciprocals proves that EVERY left weight is negative and EVERY right weight positive. No parity or sign oracle is supplied. The proof also derives injectivity of the selected labels from their separation.

For a feasible point of the ORIGINAL mean-centered H system, the slack polynomial has degree at most 2k, is nonnegative at every selected node, and is nonzero because its average over all m labels is one. There are 2k+2 selected nodes. Reusing #286 therefore finds a positive polynomial value at a node of EACH explicitly identified side, i.e. a strictly slack original row in each (k+1)-set. Neither full side can be tight.

Every proper subset S of either side has cardinality at most k and is proper among all original labels. Reusing the accepted #285 squared-root construction gives a feasible x with row_i(x)=1 exactly for i in S. This establishes minimality, not just incompatibility. It retains all original inequalities and averages over all original labels, including unselected ones. Arbitrarily spaced real parameters are permitted, and k=0 is a valid degenerate row statement.

The standalone file preserves the full two accepted helper namespaces byte-for-byte. The new theorem has an import/open-only public preamble with explicit let formulas and no local target definitions. Five transitive axiom printouts cover both reused chains and the new sign/minimality conclusion. No proof admissions, target import, verifier change, or altered Lean/Mathlib pin.

This closes the explicit interleaved-sign/minimality interface. Counting a large indexed family, establishing the desired polytopal realization hypotheses, and feeding the count into #281 are separate. No uniformly short original-edge route or solution of Polynomial Hirsch is asserted. The classical geometry is not claimed historically novel.

Local Lean/Lake is absent and release-host DNS fails. The source and exact rational tests are not local Lean verification. One prepared final NEW top-level PR comment requests the existing pinned compile/axiom/publication gate; any actual failure must be preserved rather than hidden or used for speculative hosted iteration.
