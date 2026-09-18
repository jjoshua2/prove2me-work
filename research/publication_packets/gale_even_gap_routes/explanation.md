# From selected-set even gaps to bounded exchanges

The accepted #306 route takes increasing hole enumerations and their alternating indexed parity as inputs. This packet derives those inputs from the actual selected finite-set predicate used in #302, and transfers the entire output back to the same Fin m labels. It does not duplicate the numerical root-polynomial/parity proof or claim it is accepted.

Let H be the unselected labels of S, and enumerate H increasingly as h_i. The new exact counting identity is

    card {s in S | s < h_i} + i = h_i.

The holes below h_i are exactly the image of Finset.Iio i. The selected and unselected labels below h_i partition Finset.Iio h_i, which proves the equality. For two holes, the difference of the two selected-prefix counts is exactly the number of selected labels strictly between them. Thus the literal even-gap predicate is equivalent to h_i mod 2 = (b+i) mod 2 for one b in {0,1}. Both implications are proved, including empty complements. No predecessor/separation/phase oracle is required.

Mathlib's orderEmbOfFin enumerates the ACTUAL complement, whose size is derived to be m-d. Apply the full accepted #306 construction to the two resulting natural-valued increasing lists. Its route packs each phase, crosses the packed anchors by one label exchange, reverses the second packing and removes stationary steps, with at most 2*(m-d)+1 exchanges. This prior proof is included unchanged except its public root alias and omitted printouts; it is not registered again.

For every intermediate hole configuration, lift each in-range natural value to Fin m, identify its image with the exact complement, and use the reverse parity implication to recover the selected-set even-gap predicate. The encoding/decoding identities preserve all cardinalities, endpoints and intersections. Consequently every nontrivial transition exchanges exactly one ORIGINAL finite selected label. No modulo wraparound is used to hide out-of-range data.

The public statement assumes only the endpoint finite sets, their equal cardinality and literal even-gap predicate. It does not ask for their enumeration, a parity phase, legal move sequence or path bound. Empty universes, full selected sets, empty selected sets and equal endpoints remain valid. The constructed walk need not be shortest, target-preserving or globally injective.

This closes the finite-set input/output bridge between accepted #306 and the separately owned #302 numerical/parity catalogue. It is still an ORDER-ONLY theorem: equivalence with actual moment vertices and transport to original exposed edges are not secretly premises or conclusions here. Once the separate geometry is fully verified, its exact types can be composed with this selected-set route without an assumed short exchange schedule. This is not an unrestricted Polynomial Hirsch theorem or a new best classical diameter bound.

The standalone proof uses an imports/options-only public preamble, an exact top-level solution type, and five new transitive axiom printouts. Its accepted dependency bodies are unchanged. Local Lean/Lake is unavailable; source inspection and exact finite regression are not Lean verification. One prepared new PR-comment gate is requested. Any compiler failure must be preserved rather than iterated through speculative hosted edits. The committed pin, strict platform-version guard, workflows, allowlist, duplicate controls and credential separation remain unchanged.
