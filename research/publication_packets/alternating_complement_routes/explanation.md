# Alternating complements: a coefficient-independent exchange route

This packet proves a concrete positive route theorem. Its inputs are two ordered alternating-parity complements, not a graph, an exchange sequence, or a bound on numerical score gains. It includes both starting-parity classes. The original moment-geometry interpretation is explained below but is NOT silently included in the public Lean type.

## Construction and actual bound

Write the r unselected labels as h_0<...<h_(r-1). If their starting parity is b in {0,1}, then h_i has parity b+i. Strict increase gives h_i>=h_0+i, and parity/nonnegativity gives h_0>=b. Hence h_i>=b+i.

At stage t, replace the first t holes by b,b+1,...,b+t-1 and leave all later holes unchanged. The resulting labels remain strictly increasing: the replaced prefix is ordered, its last label is below every following old hole, and the untouched suffix was already ordered. All labels stay below m and retain their original indexed parity. Consecutive stages change only the t-th hole, or do nothing if it was already packed. Thus packing takes at most r single-label exchanges, independent of the physical distances between labels.

The phase-zero packed set is {0,...,r-1}; phase one is {1,...,r}. They differ only by removing 0 and adding r. They are therefore connected by ONE exchange, not r coordinate moves. When the endpoint phases agree this transition is stationary; when r=0 both anchors are empty. Every anchor is valid because it comes from packing a valid endpoint, so the theorem assumes no extra space for a nonexistent phase-one anchor.

Concatenate source packing, the anchor transition and reversed target packing, giving 2r+1 scheduled transitions. A finite induction removes every stationary transition, keeping endpoints and legality. The final path has L<=2r+1 and every step is nontrivial. Equal endpoints are included but the construction need not return their shortest path.

Every intermediate complement has exactly r labels. Complementing in the fixed m-label universe gives m-r selected labels. For an exchange H,K, their union has r+1 labels; the intersection of the selected complements is the complement of that union, with m-r-1 labels. This proves both sides of the original-label exchange accounting without an assumed cardinality oracle.

## Relation to the moment-polytope route problem

For a sorted moment-parameter sequence, the classical even-gap condition says that the number of selected roots between any two unselected labels is even. If the holes are h_i<h_j, that number is h_j-h_i-(j-i). Consequently this condition is equivalent to alternating indexed hole parity. This equivalence and the numerical-to-original-geometry catalogue are the separate owned #302 interface; this packet does not edit or retrigger that work.

The written geometric composition would use r=m-d, accepted #299 to obtain actual vertices from admissible root sets, and accepted #295 to turn one-label root exchanges into exposed original edges. It would give the class bound 2(m-d)+1, including both normalization signs, once the exact input enumeration and legality transport are formally bound. That ORIGINAL-space all-vertex composition is not claimed Lean-verified by the present combinatorial theorem. No polynomial bound for arbitrary carriers follows from a moment-family argument.

Classical cyclic-polytope diameter results are sharper, including A.M. Maksimenko (2009), DOI10.1515/DMA.2009.003. This is a formal missing route interface, not a historically new best bound. The route need not be shortest, globally injective, target-face-preserving, or monotone for the numerical target score. Those properties are not required by the stated existence bound, and adverse finite cases are retained in the tests.

## Verification boundary

The standalone source uses only Mathlib and defines its helpers within the proof file. The public preamble contains only import/settings, and the top-level solution type is copied exactly into problem.json. Five axiom printouts cover the lower-bound, one-coordinate exchange, cross-phase anchor, full route, and public root. No admissions, self-import, assumed path or new axiom.

No local Lean/Lake was found and the compiler-host DNS check failed. Static comparisons and exact-rational tests are NOT Lean compilation. The prepared packet requests one normal NEW top-level PR conversation publication comment as the final pinned compiler/axiom/platform gate. Preserve any real failure and stop rather than using repeated speculative hosted edits. Keep the Lean4.30.0/Mathlib pin, strict0.10.5 protocol check, duplicate guards, actor allowlist and verify/publish credential split unchanged.

#300 and #302 remain their owners' geometric work. #304 is already accepted and must not be resubmitted. Reserved #210 and older owned branches are untouched.
